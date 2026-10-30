-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_cyclic_secret_sharing
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.cyclic_secret_sharing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:37:12.914751+00:00
-- url     : https://prove2.me/theorems/0e3660bc-ee97-458d-a795-a11acc728acc
-- title:
--   Unnumbered odd/even cyclic-group secret-sharing comparison, Eq.(72)
-- statement:
--   Let $N\ge1$ and perform all arithmetic modulo $N$. Define $$V|g\rangle=N^{-1/2}\sum_{h\in\mathbb Z_N}|h,g-h,g-2h\rangle.$$ This is an isometry. If $N$ is odd, every single-site erasure has an exact CPTP recovery chosen independently of the logical input. If $N$ is even, erasure of the third site is not correctable: multiplication by two is not invertible and the lost site reveals logical parity. The statement concerns normalized finite cyclic codes; continuous idealizations are separately deferred.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 19, Unnumbered odd/even cyclic-group secret-sharing comparison, Eq.(72)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.19: odd cyclic orders correct any one erasure; even positive orders leak parity
through the third site. The continuous/non-normalizable idealizations are deferred separately. -/
theorem cyclic_secret_sharing (N : ℕ) [NeZero N] :
    (cyclicEncoding N)ᴴ * cyclicEncoding N = 1 ∧
    (Odd N → ∀ i : Fin 3,
      ∃ R : Superop (Fin 3 → ZMod N) (ZMod N), IsChannel R ∧
        ∀ X, R (uniformErase {i} (fun _ => (0 : ZMod N)) (conjSuperop (cyclicEncoding N) X)) = X) ∧
    (Even N → ¬ ∃ R : Superop (Fin 3 → ZMod N) (ZMod N), IsChannel R ∧
      ∀ X, R (uniformErase {2} (fun _ => (0 : ZMod N)) (conjSuperop (cyclicEncoding N) X)) = X) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
