-- Prove2me | Theorems.Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_of_split_away_of_forall_isUnit
-- name    : QuaternionAlgebra.isDefiniteRamifiedExactlyAt_of_split_away_of_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/251e41c2-e966-55e1-aa30-ab35fc7dc633
-- title:
--   Division quaternion algebra split away from p is definite
-- statement:
--   Let $a,b$ be nonzero rationals and let $p$ be a prime. Assume two hypotheses about the rational quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ with $i^2=a$, $j^2=b$: first, that every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]$ is a unit, i.e. the algebra is a division algebra; second, that for every height-one prime $v$ of the ring of integers $\mathcal{O}_{\mathbb{Q}}$ with $p \notin v$, it is *not* the case that every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ (the $v$-adic completion of $\mathbb{Q}$) is a unit, i.e. the completion at such $v$ fails to be a division algebra. The conclusion is the predicate [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p`](def/QuaternionAlgebra_EichlerOrder.html#L87), which by definition asserts three things: $a<0$; $b<0$; and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit if and only if $p$ lies in the prime ideal $v$. Thus the algebra is definite and its set of finite ramified places is exactly $\{p\}$.
--
--   This is the standard characterisation of the definite quaternion algebra over $\mathbb{Q}$ ramified exactly at $\{p,\infty\}$ from local data: a rational quaternion division algebra that splits at every finite place away from $p$ must be definite and ramified precisely at $p$. It feeds the construction of such an algebra together with a maximal order, used in the study of endomorphism algebras of supersingular elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_of_split_away_of_forall_isUnit.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isDefiniteRamifiedExactlyAt_of_split_away_of_forall_isUnit
    (a b : ℚ) (p : ℕ) (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (hsplit : ∀ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∉ v.asIdeal →
      ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p := by sorry
