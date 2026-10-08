-- Prove2me | Theorems.Thm_RobustMNL_Static_convex_combination
-- name    : RobustMNL.Static.convex_combination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:22.071456+00:00
-- url     : https://prove2.me/theorems/acfbd52e-6875-4548-bb7e-156d035c43b5
-- title:
--   Proof of Lemma 3.1, p. 6 — f(A ∪ {i}, v) is a convex combination of rᵢ and f(A, v)
-- statement:
--   Let $v = (v_0, v_1, \dots, v_n) \in \mathbb R^{n+1}_{++}$, let $A \subseteq \mathcal A$ be an assortment and let $i \notin A$ be a product. Then the expected revenue of $A \cup \{i\}$ is the following convex combination of the revenue $r_i$ and the expected revenue $f(A, v)$:
--   $$f(A \cup \{i\}, v) = \frac{v_i}{v_0 + v_i + \sum_{\ell\in A} v_\ell}\cdot r_i + \frac{v_0 + \sum_{\ell \in A} v_\ell}{v_0 + v_i + \sum_{\ell\in A} v_\ell}\cdot f(A, v).$$
--
--   The two weights are positive and add up to one, so $f(A\cup\{i\}, v)$ lies between $r_i$ and $f(A,v)$. This identity is the whole content of Lemma 3.1.
--
--   **Formalization Note** Products are `Fin n` (Lean index $i$ is the paper's product $i+1$); $v_0$ is `p.1` and $v_i$ is `p.2 i`. The revenues $r$ are arbitrary reals, a harmless generalization of the paper's $r_i > 0$.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Proof of Lemma 3.1, p. 6, display

import Mathlib
import Definitions.Def_RobustMNL_Static_Model

namespace RobustMNL.Static

theorem convex_combination {n : ℕ} (r : Fin n → ℝ) (p : ℝ × (Fin n → ℝ)) (hp : IsPos p)
    (A : Finset (Fin n)) (i : Fin n) (hi : i ∉ A) :
    rev r (insert i A) p =
      p.2 i / (p.1 + p.2 i + ∑ ℓ ∈ A, p.2 ℓ) * r i
        + (p.1 + ∑ ℓ ∈ A, p.2 ℓ) / (p.1 + p.2 i + ∑ ℓ ∈ A, p.2 ℓ) * rev r A p := by sorry

end RobustMNL.Static
