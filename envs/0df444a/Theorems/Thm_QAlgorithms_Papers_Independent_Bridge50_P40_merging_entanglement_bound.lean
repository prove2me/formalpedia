-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_merging_entanglement_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.merging_entanglement_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:58:50.982363+00:00
-- url     : https://prove2.me/theorems/a5e50983-b8f5-48af-97d8-d9bd2085fb0d
-- title:
--   Finite-block entanglement-rate strong converse
-- statement:
--   All registers are finite and nonempty. Density operators have trace one, pure states are normalized, all entropies and logarithms are in base two, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Write $S_a$ for Petz Rényi entropy, with support projection at order zero and the von Neumann limit at order one; $S_\infty(\rho)=-\log_2\lambda_{\max}(\rho)$.
--
--   Let $\psi^{ABR}$ be one fixed normalized pure source, with Alice holding $A$, Bob holding $B$, and inaccessible reference $R$. An $n$-copy merging protocol starts with $\psi^{\otimes n}\otimes\Phi_K$ and targets $\Phi_L\otimes\psi^{\otimes n}$, with both source shares at Bob and the same reference retained. Here $n\ge1$ and $K,L\ge1$ are arbitrary integer Schmidt ranks. Let $f(P)$ be the actual complete-output root fidelity and $0\le F\le1$ any lower bound on $f(P)$. All source entropies below are single-copy entropies.
--
--   For every such LOCC protocol and $1<a\le2$,
--
--   $$
--   F\le2^{\frac{n(a-1)}{2a}\left[\frac{\log_2K-\log_2L}{n}+S_{2-a}(B)_\psi-S_{1/(2-a)}(AB)_\psi\right]}.
--   $$
--
--   At $a=2$, the two entropies are respectively log support rank and min-entropy. Signed entanglement consumption and arbitrary classical communication are permitted. The bound includes zero fidelity.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 8, Theorem 8, equations (37) and (44)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.8--9, Theorem 8, (37)/(44): entanglement-rate converse on n
copies of a fixed normalized single-copy source; arbitrary positive K,L and LOCC. -/
theorem merging_entanglement_bound {A B R : Type}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi)
    (n : ℕ) (hn : 0 < n) (P : RankMergingCode A B n)
    (F a : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hF : F ≤ mergingFidelity psi n P.K P.L P.operation)
    (ha : 1 < a) (ha2 : a ≤ 2) :
    F ≤ (2 : ℝ) ^ ((n : ℝ) * (a - 1) / (2 * a) *
      (P.rate + renyiEntropy (2 - a) (traceLeft (traceLeft (pureDensity psi))) -
        reciprocalEntropy a (traceLeft (pureDensity psi)))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
