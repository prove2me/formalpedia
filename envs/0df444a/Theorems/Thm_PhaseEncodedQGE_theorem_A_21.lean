-- Prove2me | Theorems.Thm_PhaseEncodedQGE_theorem_A_21
-- name    : PhaseEncodedQGE.theorem_A_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:51:38.115211+00:00
-- url     : https://prove2.me/theorems/d3743300-dd03-4964-851b-55e2a4d41c00
-- title:
--   Theorem A.21 — Y-mixer layer determination of the odd-reading histogram
-- statement:
--   Suppose $0<\eta<\pi$, $t=\tan(\eta/2)>1$, $\sin\gamma\ne0$ and that $1,\ \sin^2\gamma,\ t^2,\ t^2\sin^2\gamma$ are linearly independent over $\mathbb Q$. For cubic graphs on $n$ vertices with the degree-aware preparation and the Y mixer at one repetition (PE-Y1):
--
--   1. on every $m$-defect layer the first-order value $p_1(x)/p_0(x)$ determines the odd readings $(q_3-q_0,q_2-q_1)^{\mathrm{in}}$ and $(q_3-q_0,q_2-q_1)^{\mathrm{out}}$ of the profile of $D$;
--   2. for all sufficiently small $\beta>0$, the sorted readout restricted to the ranks $K_{m-1}(n)+1,\dots,K_m(n)$ determines the histogram of the odd readings over all $m$-subsets of $V(G)$.
--
--   At the schedule $(\eta,\gamma)=(23/8,2)$ the hypotheses hold for every $n$, and the PE-X1 value and the PE-Y1 value of one outcome together determine its profile for every $n$ (among outcomes with the same number of defects).
--
--   Differences from the source:
--   - generalization: outcomes of the layer of one graph G → outcomes of the layers of two cubic graphs G, G′ on the same n vertices; reason: taking G′ = G gives the paper's statement; the first-order value depends only on the profile, so the paper's argument is graph-independent
--   - encoding: for all sufficiently small $\beta>0$ (for the given graphs) → one $\beta_0>0$ chosen before the cubic graphs $G,H$ on $\mathrm{Fin}\,n$; reason: for fixed n there are finitely many labelled graphs, so the uniform and the per-pair readings are the same claim
--   - reading: the PE-X1 value and the PE-Y1 value of one outcome determine its profile → two outcomes (of cubic graphs on the same n) with equal |D| and equal PE-X1 and PE-Y1 values have equal profiles; reason: the theorem is about the m-defect layer and profile recovery uses |D| (Corollary A.19, 'Given |D| and n')
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.6, p.21 (PDF p.22), Theorem A.21 (= Theorem 3.3(Y), p.7)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_SortedReadout
import Definitions.Def_PhaseEncodedQGE_Profile
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Theorem A.21, layer determination for the Y-mixer member (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. A.1.6, p.21).

Suppose `t > 1`, `sin γ ≠ 0` and that `1, sin² γ, t², t² sin² γ` are linearly independent over `ℚ`.
Then on every `m`-defect layer the PE-Y1 first-order value `p₁(x)/p₀(x)` determines the odd readings
`(q_3 − q_0, q_2 − q_1)^in` and `(q_3 − q_0, q_2 − q_1)^out` of the profile of `D`. Consequently, for
all sufficiently small `β > 0`, the sorted readout restricted to the ranks `K_{m−1}(n) + 1, …, K_m(n)`
determines the histogram of the odd readings over all `m`-subsets of `V(G)`. At the schedule the
hypotheses hold for every `n` by Lemma A.20, and together with Theorem A.8 the PE-X1 value and the
PE-Y1 value of one outcome determine its profile for every `n`.

**Formalization Note** Degree-aware preparation, cubic graphs on `Fin n`, `0 < η < π` (standing
assumption of §2, p.5). Values are compared across two cubic graphs on the same `n` (`G' = G` is the
single-graph reading). "Determines the histogram" is one `β₀` for all `β ∈ (0, β₀)` and all cubic
`G, H`. The schedule is `(η, γ) = (23/8, 2)`; the last clause compares two outcomes of the same
layer (`|D| = |D'|`). -/
theorem theorem_A_21 :
    (∀ (n m : ℕ) (η γ : ℝ), 0 < η → η < Real.pi → 1 < Real.tan (η / 2) → Real.sin γ ≠ 0 →
      LinearIndependent ℚ ![(1 : ℝ), Real.sin γ ^ 2, Real.tan (η / 2) ^ 2,
        Real.tan (η / 2) ^ 2 * Real.sin γ ^ 2] →
      (∀ G G' : SimpleGraph (Fin n), IsCubic G → IsCubic G' → ∀ x x' : Outcome n,
        (defects x).card = m → (defects x').card = m →
        firstOrder (degPrep G η) .Y 1 G γ x = firstOrder (degPrep G' η) .Y 1 G' γ x' →
        oddIn G (defects x) = oddIn G' (defects x') ∧
          oddOut G (defects x) = oddOut G' (defects x')) ∧
      (∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        block (degPrep G η) .Y 1 G γ β m = block (degPrep H η) .Y 1 H γ β m →
        oddHist G m = oddHist H m)) ∧
    (0 < (23 / 8 : ℝ) ∧ (23 / 8 : ℝ) < Real.pi ∧ 1 < Real.tan ((23 / 8 : ℝ) / 2) ∧
      Real.sin 2 ≠ 0 ∧
      LinearIndependent ℚ ![(1 : ℝ), Real.sin 2 ^ 2, Real.tan ((23 / 8 : ℝ) / 2) ^ 2,
        Real.tan ((23 / 8 : ℝ) / 2) ^ 2 * Real.sin 2 ^ 2]) ∧
    (∀ (n : ℕ) (G G' : SimpleGraph (Fin n)), IsCubic G → IsCubic G' → ∀ x x' : Outcome n,
      (defects x).card = (defects x').card →
      firstOrder (degPrep G (23 / 8)) .X 1 G 2 x = firstOrder (degPrep G' (23 / 8)) .X 1 G' 2 x' →
      firstOrder (degPrep G (23 / 8)) .Y 1 G 2 x = firstOrder (degPrep G' (23 / 8)) .Y 1 G' 2 x' →
      profile G (defects x) = profile G' (defects x')) := by sorry

end PhaseEncodedQGE
