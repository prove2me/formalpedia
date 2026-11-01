-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P49_depolarizedCloning_weakAdditivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P49.depolarizedCloning_weakAdditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:28:16.254275+00:00
-- url     : https://prove2.me/theorems/5dd9e2b3-df30-4c2a-b0ac-194bd3ed09c5
-- title:
--   Section III-A, unnumbered: weak additivity of the depolarized cloning channel
-- statement:
--   Let $\ell\ge3$ be an integer, $\lambda=(\ell-1)/(\ell+1)$, and define the depolarizing map on all $d\times d$ operators by $P_d^\lambda(X)=\lambda X+(1-\lambda)\operatorname{Tr}(X)I_d/d$. For the complete symmetric cloning output,
--
--   $$
--   P_\ell^\lambda\circ\mathrm{Cl}_{1,\ell-1}=\mathrm{Cl}_{1,\ell-1}\circ P_2^\lambda,
--   \qquad
--   \chi\bigl((P_\ell^\lambda\circ\mathrm{Cl}_{1,\ell-1})^{\otimes n}\bigr)
--   =n\chi(P_\ell^\lambda\circ\mathrm{Cl}_{1,\ell-1})\quad(n\ge1).
--   $$
--
--   The composition is CPTP, and the intertwining identity holds on every operator. This is the source's weak-additivity aside at its specified parameter and local dimension range.
--
--   **Formalization Note** The accepted depolarizing map takes the noise probability $p=1-\lambda=2/(\ell+1)$, not $\lambda$.
-- source:
--   An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels, arXiv:0903.1638v7, PDF p. 4, Section III-A, unnumbered (continued p.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P49

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Support50.P01
  (unruhSectorDilation unruhWeight unruhBlockDilation unruhBlockWeight
   unruhReceiver unruhReceiverEntropy)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.QuditFidelity (depolarizingMap)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4--5, Section III-A: ell>=3, the specified depolarizing parameter,
the intertwining identity on all operators, and weak Holevo additivity. -/
theorem depolarizedCloning_weakAdditivity (k : ℕ) (_hk : 1 ≤ k) :
    depolarizedCloner k =
      cloner k ∘ depolarizingMap 2 (by omega) (2 / (k+3 : ℝ)) ∧
    WeakHolevoAdditive (depolarizedCloner k) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P49

end
