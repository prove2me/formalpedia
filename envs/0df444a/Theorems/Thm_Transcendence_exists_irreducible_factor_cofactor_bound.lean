-- Prove2me | Theorems.Thm_Transcendence_exists_irreducible_factor_cofactor_bound
-- name    : Transcendence.exists_irreducible_factor_cofactor_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-27T07:58:43.04845+00:00
-- url     : https://prove2.me/theorems/5e9f740b-cc7d-407a-a9a2-308e5c4e41ca
-- title:
--   The cofactor of the smallest irreducible factor is not small (the multiplicative step of Gel'fond's lemma)
-- statement:
--   Let $P \in \mathbb{Z}[X]$ have positive degree and let $\theta \in \mathbb{C}$. Then $P = Q^{e} R$ with $Q, R \in \mathbb{Z}[X]$, $Q$ irreducible of positive degree, $e \ge 1$, and
--
--   $$1 \le 2^{\deg Q \deg R}\, M(Q)^{\deg R}\, M(R)^{\deg Q}\, |R(\theta)|,$$
--
--   where $M$ is the Mahler measure. Take for $Q$ a non-constant irreducible factor of $P$ at which $|Q(\theta)|$ is least, and for $e$ its multiplicity. Every irreducible factor of $R$ is then a constant or coprime to $Q$, and `Transcendence.norm_resultant_le_max_norm_eval` bounds its value at $\theta$ from below; the bound is multiplicative, so it passes to $R$.
-- source:
--   The multiplicative step of Gel'fond's lemma (A. O. Gel'fond, Transcendental and Algebraic Numbers, 1952), as in M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §3, Lemme 2. Formal proof: Diaz modulus mission, 27 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- The cofactor of the smallest irreducible factor is not small (the multiplicative step of
Gel'fond's lemma).

Let `P ∈ ℤ[X]` have positive degree and let `θ ∈ ℂ`. Among the non-constant irreducible factors of
`P`, let `Q` be one at which `|Q(θ)|` is least, let `e` be its multiplicity, and write
`P = Q^e R`. Every irreducible factor `T` of `R` either is a constant, and then trivially satisfies
the bound below, or is coprime to `Q` with `|Q(θ)| ≤ |T(θ)|`; the Liouville inequality through the
resultant then bounds `|T(θ)|` from below. The bound is multiplicative in `T`, so it passes to
`R`: `1 ≤ 2^(deg Q · deg R) · M(Q)^(deg R) · M(R)^(deg Q) · |R(θ)|`, with `M` the Mahler measure. -/
theorem exists_irreducible_factor_cofactor_bound (P : Polynomial ℤ) (hP : 0 < P.natDegree)
    (θ : ℂ) :
    ∃ (Q R : Polynomial ℤ) (e : ℕ), Irreducible Q ∧ 0 < Q.natDegree ∧ 0 < e ∧ P = Q ^ e * R ∧
      1 ≤ 2 ^ (Q.natDegree * R.natDegree) *
        (Q.map (Int.castRingHom ℂ)).mahlerMeasure ^ R.natDegree *
        (R.map (Int.castRingHom ℂ)).mahlerMeasure ^ Q.natDegree * ‖Polynomial.aeval θ R‖ := by
  sorry

end Transcendence
