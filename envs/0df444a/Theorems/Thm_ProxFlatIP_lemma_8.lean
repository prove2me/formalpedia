-- Prove2me | Theorems.Thm_ProxFlatIP_lemma_8
-- name    : ProxFlatIP.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:33.94578+00:00
-- url     : https://prove2.me/theorems/eceb8e4a-327b-4c02-bca7-b197e83dddc8
-- title:
--   Lemma 8 — reduction to a polyhedron whose only integer point is an optimal solution
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ have full column rank, $b\in\mathbb Z^m$, $c\in\mathbb Q^n$. Let $x^*$ be an optimal vertex of $\mathrm{LP}(A,b,c)$, and suppose $\mathrm{IP}(A,b,c)$ is feasible. Then there exist an optimal solution $z^*$ of $\mathrm{IP}(A,b,c)$, an integral matrix $\bar A$ and an integral vector $\bar b$ such that:
--
--   1. $P(\bar A,\bar b)\subseteq P(A,b)$;
--   2. $x^*$ is a vertex of $P(\bar A,\bar b)$;
--   3. $P(\bar A,\bar b)\cap\mathbb Z^n=\{z^*\}$;
--   4. every row of $\bar A$ is a row of $A$ or the negative of one, and every row of $A$ is a row of $\bar A$.
--
--   This reduction is what turns proximity into a statement about polyhedra with exactly one integer point. Because the rows of $A$ all survive up to sign, the parameter $\Delta^\alpha$ is unchanged.
--
--   Differences from the source:
--   - generalization: the rows of Ā consist of rows of A and their negatives → also every row of A is a row of Ā; reason: the proof builds Ā as A with rows −A_{I*} appended, and Δ^α(A) = Δ^α(Ā) on p.10 needs it; the printed clause is still part of the statement
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Lemma 8, p.10

import Mathlib
import Definitions.Def_ProxFlatIP_Polyhedra

open Matrix

namespace ProxFlatIP

/-- **Lemma 8** (Celaya–Kuhlmann–Paat–Weismantel, arXiv:2211.14941v1, Lemma 8, p.10). If `x*` is an
optimal vertex of `LP(A,b,c)` and `IP(A,b,c)` is feasible, there are an optimal solution `z*` of
`IP(A,b,c)`, an integral matrix `Ā` and an integral vector `b̄` with `P(Ā,b̄) ⊆ P(A,b)`, `x*` a vertex of
`P(Ā,b̄)`, `P(Ā,b̄) ∩ ℤⁿ = {z*}`, every row of `Ā` a row of `A` or the negative of one, and every row
of `A` a row of `Ā`.

**Formalization Note.** `Ā` has any number `m'` of rows. The last clause is what the proof's
construction gives and what `Δ^α(A) = Δ^α(Ā)` (p.10) needs. "IP feasible" is the standing assumption
of §2. -/
theorem lemma_8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : FullColRank A) (b : Fin m → ℤ)
    (c : Fin n → ℚ) (xs : Fin n → ℝ) (hxs : IsLPOptimalVertex A b c xs)
    (hIP : IsIPFeasible A b) :
    ∃ zs : Fin n → ℝ, IsIPOptimal A b c zs ∧
      ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℤ) (b' : Fin m' → ℤ),
        Poly A' b' ⊆ Poly A b ∧
        LinearOptimization.IsVertex (Poly A' b') xs ∧
        Poly A' b' ∩ {x | IsIntegralPt x} = {zs} ∧
        (∀ i', ∃ i, A' i' = A i ∨ A' i' = -A i) ∧
        (∀ i, ∃ i', A' i' = A i) := by sorry

end ProxFlatIP
