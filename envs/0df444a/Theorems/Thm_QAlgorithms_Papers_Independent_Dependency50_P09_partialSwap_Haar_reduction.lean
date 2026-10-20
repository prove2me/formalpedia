-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_partialSwap_Haar_reduction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.partialSwap_Haar_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:18:30.917558+00:00
-- url     : https://prove2.me/theorems/9faff4c0-0f1b-4999-a7b3-6ccc840fdbd8
-- title:
--   Unnumbered partial-swap Haar symmetry reduction (339)–(342)
-- statement:
--   Let $d\ge2$, $p\in[0,1]$, and $\alpha\in(0,1)\cup(1,2]$. Let $\mathcal S_p$ be the partial-swap channel, $\mathcal T(\rho)=\int(U\otimes U)\rho(U\otimes U)^\dagger dU$, and $\mathcal T_{\rm map}(M)=\int\operatorname{Ad}_{(U\otimes U)^\dagger}\circ M\circ\operatorname{Ad}_{U\otimes U}dU$. Haar measure is normalized. The input marginal is constrained, rather than its purifying vector. Let $\Pi_\pm=(I\pm\mathrm{Swap})/2$ and $W_{q,d}=(1-q)2\Pi_+/[d(d+1)]+2q\Pi_-/[d(d-1)]$.
--
--   $$
--   \widehat\Upsilon_\alpha(\mathcal S_p)=\inf_{M:\,\beta(M)\le1,\ M=\mathcal T_{\rm map}(M)}\ \sup_{\psi:\,\psi_{AB}=\mathcal T(\psi_{AB})}\widehat D_\alpha(\mathcal S_p(\psi)\Vert M(\psi)),\qquad \rho=\mathcal T(\rho)\iff\rho=W_{q,d}\ \text{for some }q\in[0,1].
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** Comparisons are CP and pure inputs normalized. Map-twirl invariance is also equated to the Choi twirl (342), with input conjugate U,U and output U,U. Correlated compact-group covariance is distinct from independent one-design bicovariance.
--
--   **Round 1 domain audit** Round 1 restores the full geometric DPI order range (0,1) union (1,2]. The source invokes Proposition 27 for this reduction; (154)-(157) specify this DPI range, and no step of the twirling argument uses alpha>1. The illustrated numerical choice alpha=1+2^-4 does not restrict the subsequent symmetry assertion. The d>=2 guard remains for the source two-block Werner formula.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 20, Unnumbered partial-swap Haar symmetry reduction (339)–(342)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Unnumbered partial-swap Haar symmetry reduction (339)–(342), arXiv:2010.01058v3, PDF pp.20.
Comparisons are CP and pure inputs normalized. Map-twirl invariance is also equated to the Choi twirl (342), with input conjugate U,U and output U,U. Correlated compact-group covariance is distinct from independent one-design bicovariance.
The Proposition 27 argument applies on the full geometric DPI range (0,1) union (1,2]. -/
theorem partialSwap_Haar_reduction {d : ℕ} (hd : 2 ≤ d) (p alpha : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1)
    (halpha : (0 < alpha ∧ alpha < 1) ∨ (1 < alpha ∧ alpha ≤ 2)) :
    upsilon (geometricD alpha) (partialSwap d p) =
        haarUpsilon (geometricD alpha) (partialSwap d p) ∧
      (∀ rho : Op (Fin d × Fin d), IsDensityMatrix rho →
        (rho = haarInput rho ↔ ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ rho = werner d q)) ∧
      (∀ M : Superop (Fin d × Fin d) (Fin d × Fin d), CP M →
        ((∀ X, M X = haarMap M X) ↔ choi M = haarChoi (choi M))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
