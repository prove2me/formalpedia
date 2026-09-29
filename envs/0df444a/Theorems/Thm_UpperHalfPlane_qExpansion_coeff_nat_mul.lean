-- Prove2me | Theorems.Thm_UpperHalfPlane_qExpansion_coeff_nat_mul
-- name    : UpperHalfPlane.qExpansion_coeff_nat_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/0378d836-711c-5f9a-88ab-e8d8a771a51a
-- title:
--   Width rescaling of q-expansions: q_h = q_{Mh}^M
-- statement:
--   Fix a real $h > 0$ and a function $F : \mathbb{H} \to \mathbb{C}$, and assume: the extension of $F$ to $\mathbb{C}$ by `UpperHalfPlane.ofComplex` (which agrees with $F$ on the upper half-plane) is periodic with period $h$; $F$ is differentiable as a map of complex manifolds on $\mathbb{H}$ (`MDiff F`); and $F$ is bounded at $i\infty$ in the sense of `UpperHalfPlane.IsBoundedAtImInfty`. Let $M$ be a natural number with $M > 0$ and let $n$ be a natural number. Then the $n$-th coefficient of the $q$-expansion of $F$ computed at width $Mh$, i.e. in the uniformiser $q_{Mh} = e^{2\pi i \tau/(Mh)}$, equals the $(n/M)$-th coefficient of the $q$-expansion of $F$ at width $h$ when $M \mid n$, and equals $0$ otherwise; here $n/M$ is natural-number division and `qExpansion` is Mathlib's power series attached to the cusp function. Equivalently, since $q_h = q_{Mh}^M$, the width-$Mh$ expansion is the width-$h$ expansion read as a series in $q_{Mh}^M$.
--
--   This is the change of uniformiser at the cusp $\infty$, $q \mapsto q^{1/M}$, comparing the expansion of a form of one width with its expansion at the larger width of a finite-index subgroup. It is used in the derivation of the Sturm bound for arithmetic modular forms ([`ModularForm.sturm_bound_of_isArithmetic`](thm.html#ModularForm.sturm_bound_of_isArithmetic)) and in producing integral $q$-expansions after scaling and slashing by elements of $\Gamma_0$ ([`ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0`](thm.html#ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_qExpansion_coeff_nat_mul.lean

import Mathlib.NumberTheory.ModularForms.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped Manifold

theorem UpperHalfPlane.qExpansion_coeff_nat_mul {h : ℝ} (hh : 0 < h) {F : ℍ → ℂ} (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) h) (hhol : MDiff F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) {M : ℕ} (hM : 0 < M) (n : ℕ) : (qExpansion (M * h) F).coeff n = if M ∣ n then (qExpansion h F).coeff (n / M) else 0 := by sorry
