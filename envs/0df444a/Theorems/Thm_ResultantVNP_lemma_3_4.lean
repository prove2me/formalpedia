-- Prove2me | Theorems.Thm_ResultantVNP_lemma_3_4
-- name    : ResultantVNP.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:40:11.857784+00:00
-- url     : https://prove2.me/theorems/8470cbb4-540e-422a-b854-57955c70c100
-- title:
--   Lemma 3.4 — index occurrences in monomials of $\Phi_{n,s}$
-- statement:
--   Let $n\ge1$ and $s\in\mathbb N$. In every monomial of $\Phi_{n,s}$, each tensor index $i$ occurs a multiple of three times, counting occurrences within each factor with multiplicity. In particular, each monomial uses at most $s$ distinct indices.
--
--   **Formalization Note** For a monomial $\prod_T a_T^{\mu(T)}$ the occurrences of $i$ are $\sum_T\mu(T)\cdot(\text{multiplicity of }i\text{ in }T)$.
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: standing assumptions of Definition 2.1 (positive integer degrees, n forms in n variables) → hypotheses n ≥ 1; reason: Definition 2.1 assumes them; the resultant is undefined otherwise (no resultant exists for n = 0)
--   - encoding: indices [n] = {1, …, n} → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 3.4, p.15

import Mathlib
import Definitions.Def_ResultantVNP_charCoeff

namespace ResultantVNP

/-- **Lemma 3.4 (Index occurrences).** In every monomial of `Φ_{n,s}`, each tensor index occurs a
multiple of three times, counting occurrences within each factor with multiplicity. In particular,
each monomial uses at most `s` distinct indices.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 3.4, p.15.

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. A monomial is an exponent vector `μ` over unordered triples `T`; the occurrences of index `i` are
`∑_T μ(T)·(multiplicity of i in T)`. `n ≥ 1`. -/
theorem lemma_3_4 (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (s : ℕ)
    (μ : Sym (Fin n) 3 →₀ ℕ) (hμ : μ ∈ (charCoeff 𝓡 n s).support) :
    (∀ i : Fin n, 3 ∣ μ.sum (fun T k => k * Multiset.count i (T : Multiset (Fin n)))) ∧
    (Finset.univ.filter
        (fun i : Fin n => 0 < μ.sum (fun T k => k * Multiset.count i (T : Multiset (Fin n))))).card ≤ s := by sorry

end ResultantVNP
