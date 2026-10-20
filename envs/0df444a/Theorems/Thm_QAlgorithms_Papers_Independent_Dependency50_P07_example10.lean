-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_example10
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.example10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:37:00.589701+00:00
-- url     : https://prove2.me/theorems/057d05a9-66f1-4fe7-a8df-4eaa74d70ff2
-- title:
--   Pure-state common randomness and entanglement entropy
-- statement:
--   Let $|\psi\rangle\in A\otimes B$ and $|\phi\rangle\in A'\otimes B'$ be unit vectors on finite nonzero systems, and write $\psi=|\psi\rangle\langle\psi|$ and $\phi=|\phi\rangle\langle\phi|$. Their entanglement entropy is $E(|\psi\rangle)=H(\operatorname{Tr}_B\psi)$. Then
--
--   $$D^{(1)}(\psi,\infty)=D^{(1)}(\psi,0)=E(|\psi\rangle)=H(\operatorname{Tr}_B\psi),$$
--
--   $$D^{(1)}(\psi\otimes\phi,\infty)=D^{(1)}(\psi,\infty)+D^{(1)}(\phi,\infty).$$
--
--   For every integer $L\ge1$, also $D(\psi,\infty)=D^{(L)}(\psi,\infty)=D^{(1)}(\psi,\infty)$. All quantities use one-way communication and the paper’s common-randomness criterion. These conclusions include pure product states with entropy zero.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 17, Example 10: pure-state CR equals entanglement entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section QuantumStatements

variable {A B A2 B2 : Type} [Fintype A] [Fintype B] [Fintype A2] [Fintype B2]
  [DecidableEq A] [DecidableEq B] [DecidableEq A2] [DecidableEq B2]
  [Nonempty A] [Nonempty B] [Nonempty A2] [Nonempty B2]

/-- PDF p.17, Example 10: normalized pure states, including product states of zero entanglement;
zero communication, pure-product additivity, and all positive-block regularizations. -/
theorem example10 (psi : EuclideanSpace ℂ (A × B)) (hpsi : IsState psi)
    (phi : EuclideanSpace ℂ (A2 × B2)) (hphi : IsState phi) (L : ℕ) (hL : 0 < L) :
    fixedTotal (pureDensity psi) = fixedExcess (pureDensity psi) 0 ∧
    fixedExcess (pureDensity psi) 0 = vnEntropy (traceRight (pureDensity psi)) ∧
    fixedTotal (bipartiteProduct (pureDensity psi) (pureDensity phi)) =
      fixedTotal (pureDensity psi) + fixedTotal (pureDensity phi) ∧
    total (pureDensity psi) = blockTotal (pureDensity psi) L ∧
    blockTotal (pureDensity psi) L = fixedTotal (pureDensity psi) := by sorry

end QuantumStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
