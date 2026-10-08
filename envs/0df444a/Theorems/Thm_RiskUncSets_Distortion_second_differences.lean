-- Prove2me | Theorems.Thm_RiskUncSets_Distortion_second_differences
-- name    : RiskUncSets.Distortion.second_differences
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:28:41.769898+00:00
-- url     : https://prove2.me/theorems/ae5377d0-27db-418d-938e-d6ad06c2b3cf
-- title:
--   Proof of Lemma 4.1, p. 1489 — a submodular g that depends only on |A| has nonincreasing second differences along Aᵢ = {ω₁, …, ωᵢ}
-- statement:
--   Let $\Omega = \{\omega_1, \dots, \omega_N\}$ and let $g : 2^\Omega \to \mathbb R$ be submodular and a function of the cardinality alone ($|A| = |B|$ implies $g(A) = g(B)$; under Assumption 4.1 this says $g$ depends only on $\mathbb P\{A\} = |A|/N$). Put $A_k = \{\omega_1, \dots, \omega_k\}$ (with $A_0 = \emptyset$). Then for every $i \in \{1, \dots, N-1\}$
--   $$g(A_{i+1}) - g(A_i) \le g(A_i) - g(A_{i-1}).$$
--
--   In the proof of Lemma 4.1 this is the concavity of the piecewise-linear function $\theta$ with $\theta(\mathbb P\{A\}) = g(A)$ at the points $i/N$, which makes a law-invariant comonotonic coherent risk measure a mixture of CVaRs.
--
--   **Formalization Note** $\omega_k$ is `⟨k-1, _⟩ : Fin N`, so $A_k$ is $\{\omega : \omega < k\}$. "$g$ is a function of the probability alone" (law invariance under the uniform distribution) is the hypothesis that $g$ takes equal values on sets of equal cardinality. The paper's sentence also asserts the converse ("$g$ is submodular if and only if it satisfies this very property"); only the direction used in the proof is stated. Monotonicity, normalization and the codomain $[0,1]$ of $g$ are not needed and not assumed.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1489, proof of Lemma 4.1, second paragraph

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

namespace RiskUncSets.Distortion

theorem second_differences {N : ℕ} (g : Set (Fin N) → ℝ) (hsub : IsSubmodularSF g)
    (hlaw : ∀ A B : Set (Fin N), A.ncard = B.ncard → g A = g B)
    (i : ℕ) (hi : 1 ≤ i) (hiN : i + 1 ≤ N) :
    g {ω : Fin N | (ω : ℕ) < i + 1} - g {ω : Fin N | (ω : ℕ) < i} ≤
      g {ω : Fin N | (ω : ℕ) < i} - g {ω : Fin N | (ω : ℕ) < i - 1} := by sorry

end RiskUncSets.Distortion
