-- Prove2me | Theorems.Thm_SubmodOrder_rejection_bound
-- name    : SubmodOrder.rejection_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:38:30.498333+00:00
-- url     : https://prove2.me/theorems/e808a89b-57f9-4c67-993a-0f8c7ea83971
-- title:
--   Proof of Theorem 2, p.21 — the rejection bound $f(O_\ell\mid E(\ell-1))\le\sum_{e\in O_\ell}f(e\mid E(\ell-1))\le\tau|O_\ell|$
-- statement:
--   Let $\pi$ be a weak submodular order of $f$ with $f(\emptyset)=0$, and let $S=\{s_1,\dots,s_{k'}\}$ (in $\pi$-order, which is the order of addition) be the output of Threshold Add$(k,\tau)$ with $k'<k$. Let $T$ be any set and, for $\ell\ge1$, let $O_\ell$ be the elements of $T\setminus S$ between $s_{\ell-1}$ and $s_\ell$, and $E(\ell-1)=\{s_1,\dots,s_{\ell-1}\}$. Then for every $\ell\ge1$
--
--   $$
--   f\bigl(O_\ell\mid E(\ell-1)\bigr)\ \le\ \sum_{e\in O_\ell} f\bigl(e\mid E(\ell-1)\bigr)\ \le\ \tau\,|O_\ell| .
--   $$
--
--   The first inequality is the weak submodular order; the second holds because, when $k'<k$, every element of $T\setminus S$ was tested by Threshold Add and rejected. In the proof of Theorem 2, $T$ is an optimal set.
--
--   Differences from the source:
--   - generalization: f monotone and subadditive, T = OPT, τ = τ_i → every f with f(∅) = 0 and weak submodular order π, every set T and every real τ; reason: the argument uses only these hypotheses; it specializes to the paper's T = OPT
--   - encoding: the sets O_ℓ (elements of OPT \ S between s_{ℓ−1} and s_ℓ) and E(ℓ − 1) = {s₁, …, s_{ℓ−1}} for ℓ ≥ 1 → gapSet π S T j (elements of T \ S with exactly j elements of S before them) and prefixSet π S j (the first j elements of S in π-order), j = ℓ − 1; reason: index shift; S is scanned and filled in π-order, so its order of addition is its π-order
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, proof of Theorem 2, p.21

import Mathlib
import Definitions.Def_SubmodOrder_marginal
import Definitions.Def_SubmodOrder_IsWeakSubmodularOrder
import Definitions.Def_SubmodOrder_OracleProg
import Definitions.Def_SubmodOrder_thresholdAdd
import Definitions.Def_SubmodOrder_gapSet

namespace SubmodOrder

/-- The rejection bound (Udwani, arXiv:2107.02743v5, proof of Theorem 2, p.21: "Using weak
submodular order we have for every ℓ ≥ 1, f(Oℓ | E(ℓ − 1)) ≤ ∑_{e∈Oℓ} f(e | E(ℓ − 1)) ≤ τ|Oℓ|,
where the second inequality follows the fact that for k′ < k, elements in OPT\S did not meet
the criteria in Threshold Add (Algorithm 2).").

Let `π` be a weak submodular order of `f`, `f(∅) = 0`, and let `S` be the output of
Threshold Add(k, τ) with `|S| < k`. For every set `T` and every gap index `j`, with
`O = gapSet π S T j` (the elements of `T \ S` with exactly `j` elements of `S` before them) and
`E = prefixSet π S j` (the first `j` elements of `S`):
`f(O | E) ≤ ∑_{e ∈ O} f(e | E) ≤ τ · |O|`.

**Formalization Note.** 0-based gaps: `gapSet π S T j` is the paper's `O_{j+1}` and
`prefixSet π S j` its `E(j)`; `f(e | E)` is `marginal f {e} E`. -/
theorem rejection_bound {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (k : ℕ) (τ : ℝ)
    (f : Finset α → ℝ) (hf0 : f ∅ = 0) (hπ : IsWeakSubmodularOrder f π)
    (hlt : (OracleProg.run f (thresholdAdd π k τ)).1.card < k) (T : Finset α) (j : ℕ) :
    marginal f (gapSet π (OracleProg.run f (thresholdAdd π k τ)).1 T j)
        (prefixSet π (OracleProg.run f (thresholdAdd π k τ)).1 j) ≤
      ∑ e ∈ gapSet π (OracleProg.run f (thresholdAdd π k τ)).1 T j,
        marginal f {e} (prefixSet π (OracleProg.run f (thresholdAdd π k τ)).1 j) ∧
    ∑ e ∈ gapSet π (OracleProg.run f (thresholdAdd π k τ)).1 T j,
        marginal f {e} (prefixSet π (OracleProg.run f (thresholdAdd π k τ)).1 j) ≤
      τ * (gapSet π (OracleProg.run f (thresholdAdd π k τ)).1 T j).card := by sorry

end SubmodOrder
