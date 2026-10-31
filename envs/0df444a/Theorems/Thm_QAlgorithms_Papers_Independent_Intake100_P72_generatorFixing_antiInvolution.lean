-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P72_generatorFixing_antiInvolution
-- name    : QAlgorithms.Papers.Independent.Intake100.P72.generatorFixing_antiInvolution
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:49:00.771396+00:00
-- url     : https://prove2.me/theorems/cc2711c2-3190-4502-a88b-9cdd6b5c362b
-- title:
--   Generator-fixing linear anti-involution
-- statement:
--   Let $R$ be a unital commutative ring, let $m,n$ be positive integers, and let $\delta:\mathbb Z/m\mathbb Z\to R$ specify the periodic loop parameters. Let $B=B_{m,n}(\delta)$ be the cyclotomic Brauer algebra defined by relations (a)–(q) on page 3. There exists an $R$-linear map $\ast:B\to B$ such that
--
--   $$
--   (x^\ast)^\ast=x,\qquad (xy)^\ast=y^\ast x^\ast
--   \quad(x,y\in B),
--   $$
--
--   and $s_i^\ast=s_i$, $e_i^\ast=e_i$ for $1\le i<n$, and $t_j^\ast=t_j$ for $1\le j\le n$. This is the generator-fixing anti-involution used in the cellular theory; the statement requires no splitting or characteristic assumption.
-- source:
--   On the semisimplicity of cyclotomic Baruer algebras, II, arXiv:math/0702633v1, PDF p. 3, Lemma 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P72

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P72

universe u v

open QAlgorithms.Papers.Independent.Renew46.P16 (BMWLetter freeS freeE freeX)

/-- Lemma 2.1, arXiv:math/0702633v1, PDF p.3.
Over every unital commutative coefficient ring, a linear anti-involution fixes
all s_i, e_i and t_j. No field, splitting or characteristic restriction is used. -/
theorem generatorFixing_antiInvolution
    (R : Type u) [CommRing R] (m n : ℕ) (delta : ZMod m → R)
    (hm : 0 < m) (hn : 0 < n) :
    ∃ star : CyclotomicBrauer R m n delta →ₗ[R] CyclotomicBrauer R m n delta,
      Function.Involutive star ∧
      (∀ x y, star (x * y) = star y * star x) ∧
      (∀ g : BMWLetter n, star (brauerGenerator R m n delta g) =
        brauerGenerator R m n delta g) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P72

end
