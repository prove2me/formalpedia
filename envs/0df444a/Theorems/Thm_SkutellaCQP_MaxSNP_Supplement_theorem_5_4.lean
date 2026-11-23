-- Prove2me | Theorems.Thm_SkutellaCQP_MaxSNP_Supplement_theorem_5_4
-- name    : SkutellaCQP.MaxSNP.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:51:36.038521+00:00
-- url     : https://prove2.me/theorems/2bfe79a3-f582-41b2-9e52-be69a37f91f3
-- title:
--   Theorem 5.4 — conditional 1.3388 approximation using f₂-modified hyperplanes
-- statement:
--   Assume Conjecture 5.3 for the concrete $f_2$ modification and the actual common-normal hyperplane law. For arbitrary positive real processing times and nonnegative weights on two machines without release dates, take a feasible SDP solution within additive error $0\le\delta\le\delta_{54}$ of the SDP optimum. Here $L=\sum_jw_j\min_i p_{ij}$, $\rho_1=1.1847$, $\rho_2=1.3388$, and $\delta_{54}=3(\rho_2-\rho_1)L/(8\rho_2)$. Then the modified hyperplane law is a probability law on feasible Smith-ordered schedules and
--   $$\mathbb E\sum_jw_jC_j\le1.3388\,Z^*.$$
--   There also exist uniform finite-alphabet polynomial-time machines on rational inputs: one computes a feasible SDP solution within half that tolerance, and one uses polynomially many fair coins to implement its modified hyperplane law to any requested accuracy while preserving exactly the same approximation bound. The all-zero-weight case is included. The conjecture remains a premise, not a theorem or a numerical certificate.
--
--   Differences from the source:
--   - encoding: almost optimal SDP solution → quantified additive accuracy bounded by δ₅₄, including the zero-weight case; reason: the refined Lemma 5.2 bound absorbs this error while retaining exactly 1.3388
--   - generalization: the specified randomized approximation algorithm → the ideal guarantee on all real data plus uniform finite implementations at every requested total-variation accuracy; reason: specializing the accuracy gives the source algorithmic guarantee; finite fair coins avoid assuming exact irrational probabilities
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, p. 29, Theorem 5.4

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_SDPAlgorithm

namespace SkutellaCQP.MaxSNP.Supplement

/-- Theorem 5.4: the ideal modified hyperplane guarantee on the full real domain,
and a uniform finite binary implementation preserving the exact constant. -/
theorem theorem_5_4 (hc : Conjecture53) :
    (∀ (n : ℕ) (p : Two → Fin n → ℝ) (w : Fin n → ℝ),
      (∀ i j, 0 < p i j) → (∀ j, 0 ≤ w j) →
      ∀ (v : Vectors n) (Z δ : ℝ), 0 ≤ δ → δ ≤ tolerance54 p w →
        AlmostOptimal p w v Z δ →
        IsAssignmentLaw (modifiedLaw v) ∧
        expectedValue p w (modifiedLaw v) ≤ (3347 / 2500 : ℝ) * optimum p w) ∧
    (∃ (A : TwoInput → SDPOutput) (q : Polynomial ℕ) (B : List Bool → List Bool),
      SDPImplementation tolerance54 (fun _ _ v _ => modifiedLaw v) A q B ∧
      ∀ I k, IsAssignmentLaw (coinLaw q B I k) ∧
        expectedValue I.pr I.wr (coinLaw q B I k) ≤
          (3347 / 2500 : ℝ) * optimum I.pr I.wr) := by sorry

end SkutellaCQP.MaxSNP.Supplement
