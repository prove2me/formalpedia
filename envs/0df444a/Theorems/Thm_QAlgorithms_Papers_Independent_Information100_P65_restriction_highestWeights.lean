-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P65_restriction_highestWeights
-- name    : QAlgorithms.Papers.Independent.Information100.P65.restriction_highestWeights
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:48:31.423979+00:00
-- url     : https://prove2.me/theorems/b1c6b0d0-ece1-4bd2-bcde-1f7ab8d0f80a
-- title:
--   Lemma 3.3: Highest weights under restriction
-- statement:
--   Let $d\ge1$, let $\mu$ be a Young diagram of $N\ge0$ boxes with at most $d$ rows, and let $0\le n\le d$. For every irreducible constituent $L$ of the restriction of $V_\mu$ to the subgroup $U(n)$ acting on the first $n$ coordinates, there is a dominant integral highest weight $\nu=(\nu_1,\ldots,\nu_n)$ of $L$ satisfying
--
--   $$\nu_a\le\mu_a\qquad(1\le a\le n).$$
--
--   The assertion includes existence of a nonzero highest-weight vector in the actual constituent, with the stated diagonal weights and annihilation by the raising operators. The coordinate inequalities are empty when $n=0$. The result bounds the highest weights that can occur after restricting a representation.
--
--   **Formalization Note** Constituents are nonzero invariant simple subspaces for the derived $\mathfrak{gl}_n$ action on the constructed Schur module. This describes the same constituents as $U(n)$, since $U(n)$ is connected and its complexified Lie algebra is $\mathfrak{gl}_n$.
-- source:
--   Minimal output entropy for the channels that add or remove a box of a Young diagram, and a Pauli principle for every permutation symmetry, arXiv:2609.33498v1, PDF p. 14, Lemma 3.3: Highest weights under restriction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P65

attribute [local instance] Classical.propDecidable

/-- Lemma 3.3, highest weights under restriction (arxiv-2609.33498v1,
PDF p.14). Each actual constituent has a dominant integral highest weight
bounded coordinatewise by the first n rows of mu. -/
theorem restriction_highestWeights {d N : ℕ} (hd : 0 < d)
    (mu : QAlgorithms.Schur.Partition d N) (n : ℕ) (hn : n ≤ d)
    (L : Submodule ℂ (QAlgorithms.Schur.schurModule mu))
    (hL : RestrictedIrreducible mu n L) :
    ∃ nu : Fin n → ℤ, Antitone nu ∧
      (∃ v : QAlgorithms.Schur.schurModule mu, v ∈ L ∧ v ≠ 0 ∧
        (∀ (a : Fin d) (ha : a.val < n),
          derivedAction mu (Matrix.single a a 1) v =
            (nu ⟨a.val, ha⟩ : ℂ) • v) ∧
        (∀ a b : Fin d, a.val < n → b.val < n → a < b →
          derivedAction mu (Matrix.single a b 1) v = 0)) ∧
      ∀ a : Fin n, nu a ≤ (mu.val.rowLen a.val : ℤ) := by sorry

end QAlgorithms.Papers.Independent.Information100.P65

end
