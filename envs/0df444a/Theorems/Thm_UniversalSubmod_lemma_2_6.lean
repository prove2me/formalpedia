-- Prove2me | Theorems.Thm_UniversalSubmod_lemma_2_6
-- name    : UniversalSubmod.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:22.448192+00:00
-- url     : https://prove2.me/theorems/17f1f1f7-e3d5-4ce8-aadf-abce1dde3c87
-- title:
--   Lemma 2.6 — replacing $z$ by a random $Y$ with $\mathbb E Y=z$ costs at most $M\|p_\tau'\|_\infty\delta$
-- statement:
--   Let $f:2^{[n]}\to\mathbb R_{\ge0}$ be nonnegative submodular and let $M=\max_{S\subseteq[n]}f(S)$. Let $v_1,\dots,v_n\in\mathbb R^k$ be unit vectors and, for $z\in\mathbb R^k$ and $t\in\mathbb R$, let $R_z(t)=\{i\in[n]:\langle v_i,z\rangle\ge t\}$. Fix $z\in\mathbb R^k$ and $\delta\ge0$. Suppose that:
--
--   1. $Y=(Y_1,\dots,Y_k)$ is a random vector with independent, square-integrable coordinates, $\mathbb E[Y]=z$, and $\mathbb E[(Y_j-z_j)^2]\le\delta$ for all $1\le j\le k$;
--   2. $\tau$ is a real random variable independent of $Y$ whose law has a continuously differentiable density $p_\tau$;
--   3. $L$ is a number with $|p_\tau'(t)|\le L$ for all $t\in\mathbb R$.
--
--   Then
--   $$
--   \mathbb E_{Y,\tau}\big[f(R_Y(\tau))\big]\ \ge\ \mathbb E_\tau\big[f(R_z(\tau))\big]-M\,L\,\delta .
--   $$
--   With $L=\|p_\tau'\|_\infty$ this is the printed bound $\mathbb E_{Y,\tau}[f(R_Y(\tau))]\ge\mathbb E_\tau[f(R_z(\tau))]-M\|p_\tau'\|_\infty\delta$.
--
--   This is the discretization step: a Gaussian normal $z$ may be replaced by a random grid point $Y$ with the same mean at a cost that is independent of the dimension $k$, which is what allows the family of threshold sets to be enumerated.
--
--   **Formalization Note** $Y$ and $\tau$ are measurable maps on one probability space. "$\tau$ has density $p_\tau$" is the statement that the law of $\tau$ is Lebesgue measure with density $p_\tau$, a nonnegative $C^1$ function.
--
--   Differences from the source:
--   - generalization: the constant $\|p_\tau'\|_\infty$ → any $L$ with $|p_\tau'(t)|\le L$ for all $t$; reason: the inequality for every such bound specializes to the printed one at $L=\|p_\tau'\|_\infty$ when it is finite; when it is infinite the printed bound is vacuous
--   - encoding: $\delta$ unconstrained → $0\le\delta$ assumed; reason: implied by $\mathbb E[(Y_j-z_j)^2]\le\delta$ for every $k\ge1$ (the paper's dimension is always positive); it only excludes the empty-coordinate corner $k=0$
--   - encoding: $\mathbb E[Y]=z$, $\mathbb E[(Y_j-z_j)^2]\le\delta$ → each coordinate square integrable, $\int Y_j\,dP=z_j$, $\int (Y_j-z_j)^2\,dP\le\delta$; reason: the printed moments presuppose finite second moments; stating integrability keeps the integrals from being junk values
--   - encoding: $\tau$ with continuously differentiable density $p_\tau$ → $P\circ\tau^{-1}=$ Lebesgue with density $p$, $p\ge0$, `ContDiff ℝ 1 p`; reason: the meaning of a density of the law of $\tau$
--   - encoding: random variables and expectations → measurable maps on one probability space $(\Omega,P)$, expectations as Bochner integrals against $P$; reason: standing convention; every integrand is bounded or square integrable, so no integral is a junk value
--   - encoding: $\mathbb R^k$ with $\langle\cdot,\cdot\rangle$ and $\|\cdot\|$ → `EuclideanSpace ℝ (Fin k)` with its inner product and norm; reason: the same space
--   - encoding: the ground set $[n]$, subsets $S\subseteq[n]$, $f:2^{[n]}\to\mathbb R_{\ge0}$ → `Fin n`, `Finset (Fin n)`, a real-valued `f` with $f(S)\ge0$ for all $S$; reason: a relabelling of $[n]$; the same functions
--   - encoding: $\max_{S\subseteq[n]} f(S)$ → the published `OPT f` (a maximum over the nonempty finite family of all subsets); reason: the same number
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), Lemma 2.6, p.8 (proof pp.12–13)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_UniversalSubmod_threshSet

namespace UniversalSubmod

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared

/-- **Lemma 2.6** (discretization; Adamczyk, Ueltzen, Vondrák, *Optimal universal sets for
submodular functions*, manuscript of November 3, 2026, Lemma 2.6, p.8; proof pp.12–13).
Let `f : 2^[n] → ℝ≥0` be nonnegative submodular and `M = max_{S⊆[n]} f(S)`. Fix `z ∈ ℝ^k` and let
`Y = (Y₁, …, Y_k)` be a random vector with independent coordinates, `E[Y] = z` and
`E[(Y_j − z_j)²] ≤ δ` for all `j`. Let `τ` be a random variable independent of `Y` with a
continuously differentiable density `p_τ`. For unit vectors `v₁, …, vₙ ∈ ℝ^k` and
`R_z(τ) = {i : ⟨vᵢ, z⟩ ≥ τ}`,
`E_{Y,τ}[f(R_Y(τ))] ≥ E_τ[f(R_z(τ))] − M ‖p_τ'‖_∞ δ`.

**Formalization Note.** `Y` and `τ` live on one probability space `(Ω, P)`; `Y` and `τ` are
measurable; the coordinates of `Y` are square integrable (so the means and second moments in the
hypotheses are genuine, not Bochner junk values). "`τ` has density `p`" is `P.map τ = Lebesgue
with density p`, with `p` continuously differentiable and nonnegative. `‖p_τ'‖_∞` is replaced by any
bound `L` with `|p'(t)| ≤ L` for all `t` (the printed statement is the case `L = ‖p_τ'‖_∞`).
`0 ≤ δ` is added; it follows from the hypotheses whenever `k ≥ 1`. `M` is `OPT f`. -/
theorem lemma_2_6 {n k : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1)
    (z : EuclideanSpace ℝ (Fin k)) (δ : ℝ) (hδ : 0 ≤ δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → EuclideanSpace ℝ (Fin k)) (hY : Measurable Y)
    (hYind : iIndepFun (fun j ω => Y ω j) P)
    (hY2 : ∀ j, MemLp (fun ω => Y ω j) 2 P)
    (hYmean : ∀ j, ∫ ω, Y ω j ∂P = z j)
    (hYvar : ∀ j, ∫ ω, (Y ω j - z j) ^ 2 ∂P ≤ δ)
    (τ : Ω → ℝ) (hτ : Measurable τ) (hind : IndepFun Y τ P)
    (p : ℝ → ℝ) (hp : ContDiff ℝ 1 p) (hp0 : ∀ t, 0 ≤ p t)
    (hlaw : P.map τ = volume.withDensity (fun t => ENNReal.ofReal (p t)))
    (L : ℝ) (hL : ∀ t, |deriv p t| ≤ L) :
    ∫ ω, f (threshSet v z (τ ω)) ∂P - OPT f * L * δ ≤
      ∫ ω, f (threshSet v (Y ω) (τ ω)) ∂P := by sorry

end UniversalSubmod
