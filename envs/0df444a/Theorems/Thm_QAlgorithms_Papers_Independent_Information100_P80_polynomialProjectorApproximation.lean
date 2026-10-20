-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P80_polynomialProjectorApproximation
-- name    : QAlgorithms.Papers.Independent.Information100.P80.polynomialProjectorApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:17:56.562992+00:00
-- url     : https://prove2.me/theorems/a9fce8c4-30c1-4027-8971-47aeb8afd336
-- title:
--   Lemma 3 (Polynomial projector approximation)
-- statement:
--   There is an absolute constant $c>0$, independent of all registers and parameters below. Let $B,E$ have positive finite dimensions, let $\Pi$ be any orthogonal projector on $B\otimes E$, and put $\kappa=\min\{(\dim B)^2,(\dim E)^2\}$. For natural numbers $n,D$ satisfying $3\le D$ and $2D\le n$, there exists an operator $\widetilde\Pi_D$ on $B^{\otimes n}\otimes E^{\otimes n}$ such that
--   $$
--   \widetilde\Pi_D\Pi^{\otimes n}=\Pi^{\otimes n}\widetilde\Pi_D=\Pi^{\otimes n},\qquad
--   \|\widetilde\Pi_D-\Pi^{\otimes n}\|_\infty\le2^{-cD^2/n},
--   $$
--   $$
--   \|\widetilde\Pi_D\|_\pi\le(2\kappa)^D2^{n h(D/n)}.
--   $$
--
--   Here $h(t)=-t\log_2t-(1-t)\log_2(1-t)$ is binary entropy with $0\log_20=0$. The projective norm is across the regrouped bipartition $B^n:E^n$ and is induced by the two local spectral norms. All divisions in the exponents are real. Both the zero projector and the identity projector are allowed.
--
--   This gives simultaneous exponential approximation accuracy and control of the bipartite decomposition norm.
-- source:
--   Strong Converses for Quantum Channel Capacities from Blowing-Up Lemmata, arXiv:2609.11771v1, PDF p. 9, Lemma 3 (Polynomial projector approximation)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P80

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

/-- Lemma 3, PDF p.9, (41)–(42). The absolute constant precedes all dimensions.
The norm of the approximant is across B^n:E^n, rather than across individual uses. -/
theorem polynomialProjectorApproximation :
    ∃ c : ℝ, 0 < c ∧
      ∀ (B E : Type) [Fintype B] [Fintype E] [DecidableEq B] [DecidableEq E]
        [Nonempty B] [Nonempty E]
        (P : Matrix (B × E) (B × E) ℂ),
        P.IsHermitian → P * P = P →
        ∀ n D : ℕ, 3 ≤ D → 2 * D ≤ n →
          ∃ Ptilde : Matrix ((Fin n → B) × (Fin n → E))
            ((Fin n → B) × (Fin n → E)) ℂ,
            Ptilde * groupedPower P n = groupedPower P n ∧
            groupedPower P n * Ptilde = groupedPower P n ∧
            specNorm (Ptilde - groupedPower P n) ≤
              (2 : ℝ) ^ (-c * (D : ℝ) ^ 2 / (n : ℝ)) ∧
            projectiveNorm Ptilde ≤
              (2 * min ((Fintype.card B : ℝ) ^ 2) ((Fintype.card E : ℝ) ^ 2)) ^ D *
                (2 : ℝ) ^ ((n : ℝ) * binEntropy2 ((D : ℝ) / (n : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P80

end
