-- Prove2me | Theorems.Thm_PADMPriv_lemma_A6
-- name    : PADMPriv.lemma_A6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:17.985808+00:00
-- url     : https://prove2.me/theorems/916c5cdf-3f94-4fdc-89b4-3d1ceffc0dc7
-- title:
--   Lemma A6 — privacy amplification by iteration [FMTT18]
-- statement:
--   Let $\alpha>1$ and let $T_1,\dots,T_n$, $T'_1,\dots,T'_n$ be non-expansive operators on $\mathbb R^m$. For a common initial point $\tilde u_{(0)} = \tilde u'_{(0)}$ and a noise distribution $P_z$ on $\mathbb R^m$, consider
--   $$
--   \tilde u_{(k)} = T_k(\tilde u_{(k-1)}) + z_{(k)},\qquad \tilde u'_{(k)} = T'_k(\tilde u'_{(k-1)}) + z_{(k)},
--   $$
--   with $z_{(1)},\dots,z_{(n)}$ i.i.d. $P_z$. Let $s_{(k)}$ be real numbers with $\|T_k(u)-T'_k(u)\|_2\le s_{(k)}$ for all $u$, and let $a_{(1)},\dots,a_{(n)}\ge0$ satisfy
--   $$
--   \sum_{i\le k}s_{(i)}-\sum_{i\le k}a_{(i)}\ge0\ \text{ for every } k,\qquad \sum_{i\le n}s_{(i)}=\sum_{i\le n}a_{(i)}. \tag{49}
--   $$
--   Then
--   $$
--   D_\alpha\big(\tilde u_{(n)}\,\big\|\,\tilde u'_{(n)}\big)\le\sum_{k=1}^n R_\alpha(P_z,a_{(k)}),
--   $$
--   where $R_\alpha$ is the shifted Rényi divergence of Definition A2.
--
--   This is the engine of Theorems 4.1 and 4.2: a change at one step is spread over all later noisy steps.
--
--   **Formalization Note** In the paper $s_{(k)} := \sup_u\|T_k(u)-T'_k(u)\|_2$; here $s_{(k)}$ is any real upper bound of that supremum. Indices run over $\{0,\dots,n-1\}$; non-expansive is the published `ThreeOpSplitting.Convergence.IsNonexpansive`.
--
--   Differences from the source:
--   - generalization: s₍ₖ₎ := sup_u ‖T_k(u) − T′_k(u)‖₂ → any real s₍ₖ₎ with ‖T_k(u) − T′_k(u)‖₂ ≤ s₍ₖ₎ for all u; reason: taking s₍ₖ₎ equal to the supremum gives the source's lemma whenever the supremum is finite, and (49) cannot hold with an infinite supremum
--   - encoding: the Rényi divergence of Definition 2 → computed through dP/dQ, +∞ when P is not absolutely continuous with respect to Q; reason: equal to Definition 2 for α > 1
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Lemma A6, p.24 (cited from Feldman–Mironov–Talwar–Thakurta 2018)

import Mathlib
import Definitions.Def_PADMPriv_noisyIter
import Definitions.Def_PADMPriv_renyiDiv
import Definitions.Def_PADMPriv_shiftRenyi
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive

namespace PADMPriv

open MeasureTheory

/-- Lemma A6 (privacy amplification by iteration, [FMTT18]) of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.24.
Let `α > 1`, let `T₁, …, Tₙ, T′₁, …, T′ₙ` be non-expansive operators on `ℝᵐ`, let
`ũ₍₀₎ = ũ′₍₀₎` be a common initial point and `P_z` a noise distribution, and consider
`ũ₍ₖ₎ = T_k(ũ₍ₖ₋₁₎) + z₍ₖ₎`, `ũ′₍ₖ₎ = T′_k(ũ′₍ₖ₋₁₎) + z₍ₖ₎` with `z₍ₖ₎ ∼ P_z` independent. If
`‖T_k(u) − T′_k(u)‖₂ ≤ s₍ₖ₎` for all `u`, and `a₍ₖ₎ ≥ 0` satisfy
`∑_{i ≤ k} s₍ᵢ₎ − ∑_{i ≤ k} a₍ᵢ₎ ≥ 0` for every `k` and `∑_{i ≤ n} s₍ᵢ₎ = ∑_{i ≤ n} a₍ᵢ₎` (49), then
`D_α(ũ₍ₙ₎‖ũ′₍ₙ₎) ≤ ∑ₖ R_α(P_z, a₍ₖ₎)`.

**Formalization Note** The paper's `s₍ₖ₎ := sup_u ‖T_k(u) − T′_k(u)‖₂` is replaced by any real upper
bound `s₍ₖ₎` of that supremum (the paper's choice when the supremum is finite; (49) cannot hold
with an infinite one). Indices are `Fin n` (0-based); the laws of `ũ₍ₙ₎`, `ũ′₍ₙ₎` are images of
`P_z^{⊗n}`; non-expansive is the published `ThreeOpSplitting.Convergence.IsNonexpansive`. -/
theorem lemma_A6 {m n : ℕ} (α : ℝ) (hα : 1 < α)
    (T T' : Fin n → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hT : ∀ k, ThreeOpSplitting.Convergence.IsNonexpansive (T k))
    (hT' : ∀ k, ThreeOpSplitting.Convergence.IsNonexpansive (T' k))
    (u₀ : EuclideanSpace ℝ (Fin m)) (Pz : Measure (EuclideanSpace ℝ (Fin m)))
    [IsProbabilityMeasure Pz] (s a : Fin n → ℝ) (hs : ∀ k u, ‖T k u - T' k u‖ ≤ s k)
    (ha : ∀ k, 0 ≤ a k) (hprefix : ∀ k : Fin n, ∑ i ∈ Finset.Iic k, a i ≤ ∑ i ∈ Finset.Iic k, s i)
    (htotal : ∑ i, s i = ∑ i, a i) :
    renyiDiv α ((Measure.pi fun _ : Fin n => Pz).map (fun w => noisyIter T u₀ w n))
        ((Measure.pi fun _ : Fin n => Pz).map (fun w => noisyIter T' u₀ w n)) ≤
      ∑ k, shiftRenyi α Pz (a k) := by sorry

end PADMPriv
