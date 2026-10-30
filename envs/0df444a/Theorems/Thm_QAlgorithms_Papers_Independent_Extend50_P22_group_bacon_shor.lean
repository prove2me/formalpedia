-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_group_bacon_shor
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.group_bacon_shor
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:33:38.23217+00:00
-- url     : https://prove2.me/theorems/43bdc6e0-2291-4ad8-bb66-7ac3512e9727
-- title:
--   Unnumbered concatenated [[m²,1,m]]G code
-- statement:
--   Let $G$ be finite and $m\ge1$. Concatenate the $m$-site phase encoding with an $m$-site bit encoding of each of its outputs. Explicitly, $$V|g\rangle=|G|^{-(m-1)/2}\sum_{h_1\cdots h_m=g}\bigotimes_{i=1}^m|h_i\rangle^{\otimes m}.$$ This is an isometry from a $|G|$-dimensional logical system into $m^2$ sites of dimension $|G|$, corrects every erasure of at most $m-1$ sites, and implements logical left multiplication transversally on the first row. The construction is a group code, without a binary-stabilizer assumption.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 18, Unnumbered concatenated [[m²,1,m]]G code

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.18: G-covariant [[m^2,1,m]]_G, protecting every erased set of at most m-1 sites. -/
theorem group_bacon_shor (G : Type*) [Group G] [Fintype G] (k : ℕ) :
    let V := baconShorEncoding G k
    Vᴴ * V = 1 ∧
    (∀ S : Finset (Fin (k + 1) × Fin (k + 1)), S.card ≤ k → CorrectsGroupErasure V S) ∧
    ∀ g : G,
      basisMapMatrix (fun y : (Fin (k + 1) × Fin (k + 1)) → G =>
        fun ij => if ij.1 = 0 then g * y ij else y ij) * V =
      V * basisMapMatrix (fun h => g * h) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
