-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P49_highestIrrep_degradingConstruction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P49.highestIrrep_degradingConstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:30:50.296001+00:00
-- url     : https://prove2.me/theorems/8a4d06a0-0e48-4fc8-9851-eeb5f1d0dc6a
-- title:
--   Section IV, unnumbered: highest-irrep Choi degrading maps in the explicitly checked dimensions
-- statement:
--   Let $\ell\in\{3,4,5,6,7\}$ and put $k=\ell-2$. In the fixed occupation bases let $\Pi_{\max}$ be the projector onto the highest irreducible summand of the ordinary SU(2) tensor representation $\operatorname{Sym}^{\ell-2}(\mathbb C^2)\otimes\operatorname{Sym}^{\ell-1}(\mathbb C^2)$. The first factor is the degrading output. The projector has rank $2\ell-2$. Define the unnormalized, output-first Choi matrix and its reconstructed map by
--
--   $$
--   R_{D_\ell}=\frac{\ell}{2\ell-2}\Pi_{\max},\qquad
--   D_\ell(X)=\operatorname{Tr}_{\rm in}[(I\otimes X^T)R_{D_\ell}].
--   $$
--
--   Then $D_\ell$ is CPTP, has exactly this Choi matrix, and
--
--   $$
--   D_\ell\circ\mathrm{Cl}_{1,\ell-1}=S^c_{\ell-1}.
--   $$
--
--   The source reports exact solutions for $\ell=3,4$ and successful checks for $\ell=5,6,7$. The statement specifies the construction for exactly that set. It gives neither a universal projector-ansatz theorem nor a runtime bound.
--
--   **Formalization Note** The projector is constructed by the normalized occupation coefficients $c_{a,i}=\sqrt{\binom{k}{a}\binom{k+1}{i}/\binom{2k+1}{a+i}}$: its entry is $c_{a,i}c_{b,j}$ when $a+i=b+j$, and zero otherwise. These coefficients fix the highest-irrep phases without an arbitrary projector witness.
-- source:
--   An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels, arXiv:0903.1638v7, PDF p. 6, Section IV, unnumbered (Eqs.(24)–(26), pp.5–6)

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

/-- PDF pp.5--6, Section IV: the highest-irrep unnormalized Choi ansatz
is the degrading map for precisely the reported dimensions ell=3,4,5,6,7.
The claim is not extended to every ell and makes no runtime assertion. -/
theorem highestIrrep_degradingConstruction (k : ℕ) (_hk0 : 1 ≤ k) (_hk1 : k ≤ 5) :
    (highestProjector k)ᴴ = highestProjector k ∧
    highestProjector k * highestProjector k = highestProjector k ∧
    (highestProjector k).rank = 2*k+2 ∧
    outputFirstChoi (highestDegradingMap k) = degradingChoi k ∧
    IsChannel (highestDegradingMap k) ∧
    ∀ X, highestDegradingMap k (cloner k X) = clonerComplement k X := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P49

end
