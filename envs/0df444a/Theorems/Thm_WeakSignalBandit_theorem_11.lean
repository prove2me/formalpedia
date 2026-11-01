-- Prove2me | Theorems.Thm_WeakSignalBandit_theorem_11
-- name    : WeakSignalBandit.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:30:19.66287+00:00
-- url     : https://prove2.me/theorems/4d43ebfb-2370-4cf6-8e37-448da868a4c7
-- title:
--   Theorem 11, p.32 — Stroock–Varadhan: Markov chains with locally uniformly convergent truncated characteristics converge weakly in $C$ to the unique diffusion (corrected: uniqueness in law assumed)
-- statement:
--   Let $\iota$ be a finite set of coordinates ($\mathbb R^d$ with $d=|\iota|$, Euclidean norm). Let $a_{k,l}$ and $b_k$, $k,l\in\iota$, be bounded Lipschitz-continuous functions on $\mathbb R^d$. For each $n$, let $(Z^n_i)_{i\in\mathbb N}$ be a time-homogeneous Markov chain in $\mathbb R^d$ with transition kernel $\Pi^n$, let $K^n=n\Pi^n$, and let $a^n$, $b^n$, $\Delta^n_\epsilon$ be the truncated characteristics of $K^n$. Suppose that for all $k,l$ and all $\epsilon,R>0$,
--   $$\lim_{n\to\infty}\sup_{|z|<R}|a^n_{k,l}(z)-a_{k,l}(z)|=0,\qquad\lim_{n\to\infty}\sup_{|z|<R}|b^n_k(z)-b_k(z)|=0,\qquad\lim_{n\to\infty}\sup_{|z|<R}\Delta^n_\epsilon(z)=0.$$
--   Suppose that $Z^n_0\to z_0$ in probability and that any two solution laws of
--   $$dZ_t=b(Z_t)\,dt+\eta(Z_t)\,dB_t,\qquad Z_0=z_0,\qquad \eta\eta^\top=a,$$
--   on $\mathcal C=C([0,1],\mathbb R^d)$ coincide. Then this equation has exactly one solution law $P$,
--   and the interpolated paths $(\bar Z^n_t)_{t\in[0,1]}$ converge weakly in $\mathcal C$ to $P$: $\mathbb E[F(\bar Z^n)]\to\mathbb E_P[F]$ for every bounded continuous $F:\mathcal C\to\mathbb R$.
--
--   This is the diffusion-approximation theorem (Stroock and Varadhan, *Multidimensional Diffusion Processes*, Ch. 11; Durrett, *Stochastic Calculus*, Ch. 8) through which the paper proves Theorem 1; in its proof $d=2K$.
--
--   **Formalization Note** The SDE is encoded by its martingale problem on $[0,1]$. The Markov property is with respect to the whole past $\sigma(Z^n_0,\dots,Z^n_i)$. Deterministic starting points $z^n_0\to z_0$ are a special case of the starting condition. Locally uniform convergence is `TendstoUniformlyOn` on the open ball of radius $R$.
--
--   Differences from the source:
--   - correction: the printed theorem has no uniqueness hypothesis and a, b bounded Lipschitz are claimed to give a unique solution → added hypothesis huniq: any two solution laws of (A.10) from z₀ coincide; reason: the printed statement is false. Counterexample with d = 2, g(x, y) = min(1, |x| + |y|), b = (g, 0), a = diag(0, g), z₀ = 0: the chains Z + (g(Z)/n, ±√(g(Z)/n)) satisfy (A.7)–(A.9), and two laws solve (A.10), namely the Dirac mass at the zero path and the law of (X, W∘X), with W a Brownian motion and X the inverse of τ(x) = ∫_0^x du/g(u, W_u), which is a.s. finite. The cited Stroock–Varadhan Thm 11.2.3 and Durrett Thm 8.7.1 assume a well-posed martingale problem, and the theorem's own conclusion implies huniq, so it is the minimal repair
--   - encoding: solution of the SDE driven by a Brownian motion → solution law of the martingale problem on [0,1] tested with all smooth compactly supported f and finite products of bounded measurable functions of past values (IsDiffusionLaw); reason: Mathlib has no Itô integral; a law solves the martingale problem for (a, b) exactly when it is the law of a weak solution of the SDE with ηηᵀ = a (Ethier–Kurtz Ch. 5, Prop. 3.1, Thm 3.3)
--   - reading: converges weakly to the unique solution → a solution law L exists, every solution law equals L, and the laws converge weakly to L; reason: weak convergence identifies only the law; footnote 5 (p.32) says the SDE is determined by a up to the choice of η, i.e. uniqueness is in law
--   - encoding: weak convergence in C → convergence of the integrals of every bounded continuous F : C → ℝ; reason: the definition of weak convergence of laws on C; the paths are measurable (checked in the verification file)
--   - reading: Z̄ⁿ₀ → z₀ → Zⁿ₀ converges to z₀ in probability; reason: the page gives a deterministic limit z₀ and no initial law; this is the strongest reading, and it covers deterministic starting points z0n n → z₀ and almost sure convergence
--   - generalization: ℝ^d → EuclideanSpace ℝ ι for any finite index type ι; reason: ι = Fin d is the source's case
--   - encoding: time-homogeneous Markov chain with transition kernel Πⁿ (A.4) → IsMarkovChain: P(Z_{i+1} ∈ B | σ(Z_0,…,Z_i)) = Π(Z_i, B) a.s. for a measurable Markov kernel Π; reason: the standard meaning of (A.4)
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, Theorem 11, p.32 (cited from Stroock–Varadhan 2007, Ch. 11, and Durrett 1996, Ch. 8); (A.4)–(A.6) p.31

import Mathlib
import Definitions.Def_WeakSignalBandit_DiffusionLaw
import Definitions.Def_WeakSignalBandit_Interpolation
import Definitions.Def_WeakSignalBandit_ChainCharacteristics

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace WeakSignalBandit

/-- **Theorem 11 (Stroock–Varadhan diffusion approximation; corrected: uniqueness in law of (A.10)
is assumed).** Fix `d` (here: a finite coordinate
set `ι`). Let `a_{k,l}` and `b_k` be bounded Lipschitz-continuous functions from `ℝ^d` to `ℝ`. For
each `n`, let `(Z^n_i)_{i ∈ ℕ}` be a time-homogeneous Markov chain in `ℝ^d` with transition kernel
`Π^n`, let `K^n = nΠ^n`, and let `a^n`, `b^n`, `Δ^n_ε` be its truncated characteristics. Suppose
that for all `k, l` and `ε, R > 0`, uniformly over `|z| < R`, `a^n_{k,l} → a_{k,l}` (A.7),
`b^n_k → b_k` (A.8) and `Δ^n_ε → 0` (A.9). If `Z̄^n_0 → z₀` and (A.10) is unique in law, then
`(Z̄^n_t)_{t∈[0,1]}` converges weakly in `C` to the unique solution of
`dZ_t = b(Z_t) dt + η(Z_t) dB_t`, `Z_0 = z₀`, `a = ηηᵀ` (A.10).
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, Theorem 11, p.32 (cited from Stroock–Varadhan 2007, Ch. 11; Durrett 1996,
Ch. 8); (A.4)–(A.6) p.31.

**Formalization Note** The SDE (A.10) is encoded by its martingale problem on `[0,1]`
(`IsDiffusionLaw`), and "the unique solution" as: a solution law exists and every solution law
equals it (uniqueness in law; footnote 5, p.32). Weak convergence in `C` is convergence of
`E F(Z̄^n)` for every bounded continuous `F : C → ℝ`. `Z̄^n_0 = Z^n_0`, and `Z̄^n_0 → z₀` is
convergence in probability, which covers deterministic starting points.

**Correction** The page has no hypothesis `huniq`, and the theorem is false without it: bounded
Lipschitz `a` need not have a Lipschitz square root, and the sources it cites (Stroock–Varadhan
Thm 11.2.3, Durrett Thm 8.7.1) assume that the martingale problem is well posed. Counterexample
(`d = 2`): `g(x, y) = min(1, |x| + |y|)`, `b = (g, 0)`, `a = diag(0, g)`, `z₀ = 0`. The chains
`Z ↦ Z + (g(Z)/n, ±√(g(Z)/n))` satisfy (A.7)–(A.9), and two laws solve (A.10) from `0`: the Dirac
mass at the zero path, and the law of `(X, W ∘ X)`, where `W` is a Brownian motion and `X` is the
inverse of `τ(x) = ∫_0^x du / g(u, W_u)`, which is a.s. finite because
`E[1/(u + |W_u|)] ≤ C u^{-1/2}(1 + |log u|)` near `0`. -/
theorem theorem_11 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Sp ι → ι → ι → ℝ) (b : Sp ι → ι → ℝ)
    (ha_bdd : ∀ k l, ∃ C : ℝ, ∀ z, |a z k l| ≤ C)
    (ha_lip : ∀ k l, ∃ L, LipschitzWith L (fun z => a z k l))
    (hb_bdd : ∀ k, ∃ C : ℝ, ∀ z, |b z k| ≤ C)
    (hb_lip : ∀ k, ∃ L, LipschitzWith L (fun z => b z k))
    (T : ℕ → Kernel (Sp ι) (Sp ι)) [∀ n, IsMarkovKernel (T n)]
    (h7 : ∀ R : ℝ, 0 < R → ∀ k l,
      TendstoUniformlyOn (fun n z => truncDiff (scaledKernel (T n) n) z k l)
        (fun z => a z k l) atTop (Metric.ball 0 R))
    (h8 : ∀ R : ℝ, 0 < R → ∀ k,
      TendstoUniformlyOn (fun n z => truncDrift (scaledKernel (T n) n) z k)
        (fun z => b z k) atTop (Metric.ball 0 R))
    (h9 : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      TendstoUniformlyOn (fun n z => jumpMass (scaledKernel (T n) n) ε z)
        (fun _ => 0) atTop (Metric.ball 0 R))
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (Pr : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Pr n)]
    (Z : ∀ n, ℕ → Ω n → Sp ι) (hZ : ∀ n, IsMarkovChain (Pr n) (T n) (Z n))
    (z₀ : Sp ι)
    (hstart : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => Pr n {ω | ε < ‖Z n 0 ω - z₀‖}) atTop (𝓝 0))
    (huniq : ∀ L L' : Measure (Path ι), IsDiffusionLaw a b z₀ L → IsDiffusionLaw a b z₀ L' →
      L = L') :
    ∃ L : Measure (Path ι),
      IsDiffusionLaw a b z₀ L ∧
      (∀ L' : Measure (Path ι), IsDiffusionLaw a b z₀ L' → L' = L) ∧
      ∀ F : Path ι →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, F (interpPath n (fun i => Z n i ω)) ∂(Pr n)) atTop
          (𝓝 (∫ x, F x ∂L)) := by sorry

end WeakSignalBandit
