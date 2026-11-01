-- Prove2me | Theorems.Thm_SubmodOrder_inequality_5
-- name    : SubmodOrder.inequality_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:41.130365+00:00
-- url     : https://prove2.me/theorems/57ed1071-219a-4e22-a12d-a23916a1dc13
-- title:
--   Inequality (5), proof of Theorem 2, p.21 — $\mathrm{OPT}\le f(\mathrm{OPT}\cup S)\le f(S)+\sum_{\ell}f(O_\ell\mid E(\ell-1))$ (corrected: last term)
-- statement:
--   Let $f$ be monotone with weak submodular order $\pi$, let $S=\{s_1,\dots,s_{k'}\}$ be listed in $\pi$-order and let $T$ be any set. For $\ell=1,\dots,k'+1$ let $O_\ell$ be the elements of $T\setminus S$ between $s_{\ell-1}$ and $s_\ell$ (no bound for $\ell=1$ on the left and for $\ell=k'+1$ on the right), and $E(\ell-1)=\{s_1,\dots,s_{\ell-1}\}$. Then
--
--   $$
--   f(T)\ \le\ f(T\cup S)\ \le\ f(S)+\sum_{\ell=1}^{k'+1} f\bigl(O_\ell\mid E(\ell-1)\bigr).
--   $$
--
--   The first inequality is monotonicity; the second is Corollary 2 applied to the interleaved partition $\{O_1,\{s_1\},O_2,\dots,\{s_{k'}\},O_{k'+1}\}$ of $T\cup S$. In the proof of Theorem 2, $S$ is the output of Threshold Add and $T$ an optimal set.
--
--   Differences from the source:
--   - correction: the sum ∑_{ℓ∈[k′]} f(O_ℓ | E(ℓ − 1)) → the sum over ℓ ∈ [k′+1], including f(O_{k′+1} | E(k′)); reason: the partition {O₁, {s₁}, …, {s_{k′}}, O_{k′+1}} has k′ + 1 blocks O; without the last term (5) is false: f additive with f({1}) = 1, f({2}) = 0.1, π = (1, 2), k = 2, τ ∈ (0.1, 1] gives S = {1}, OPT = f({1,2}) = 1.1, O₁ = ∅, O₂ = {2}, and (5) reads 1.1 ≤ 1
--   - generalization: S the output of Threshold Add, T = OPT, f monotone subadditive with f(∅) = 0 → any sets S and T, f monotone with a weak submodular order; reason: the inequality uses only monotonicity and Corollary 2; it specializes to the paper's S and OPT
--   - encoding: the sets O_ℓ (elements of OPT \ S between s_{ℓ−1} and s_ℓ) and E(ℓ − 1) = {s₁, …, s_{ℓ−1}} for ℓ ≥ 1 → gapSet π S T j (elements of T \ S with exactly j elements of S before them) and prefixSet π S j (the first j elements of S in π-order), j = ℓ − 1; reason: index shift; S is scanned and filled in π-order, so its order of addition is its π-order
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, inequality (5), proof of Theorem 2, p.21

import Mathlib
import Definitions.Def_SubmodOrder_marginal
import Definitions.Def_SubmodOrder_IsWeakSubmodularOrder
import Definitions.Def_SubmodOrder_gapSet

namespace SubmodOrder

/-- Inequality (5) (Udwani, arXiv:2107.02743v5, proof of Theorem 2, p.21: "From monotonicity of
the function we have, OPT ≤ f(OPT ∪ S). … Applying Corollary 2 on OPT ∪ S with Ej = sj for
j ∈ [k′] we have, OPT ≤ f(E(k′)) + ∑_{ℓ∈[k′]} f(Oℓ | E(ℓ − 1)), = f(S) + ∑_{ℓ∈[k′]} f(Oℓ | E(ℓ − 1)).
(5)"), with the last term of the sum restored.

For a monotone `f` with weak submodular order `π` and any sets `S` (with `k′ = |S|`) and `T`:
`f(T) ≤ f(T ∪ S)` and `f(T ∪ S) ≤ f(S) + ∑_{ℓ ∈ [k′+1]} f(O_ℓ | E(ℓ − 1))`, where `O_ℓ` is the set
of elements of `T \ S` between the `(ℓ−1)`-th and the `ℓ`-th element of `S` in `π`-order and
`E(ℓ − 1)` the first `ℓ − 1` elements of `S`.

**Formalization Note.** 0-based gaps: the summand for `j ∈ {0, …, k′}` is
`f(O_{j+1} | E(j))` with `O_{j+1} = gapSet π S T j` and `E(j) = prefixSet π S j`. The printed
sum stops at `ℓ = k′` and omits `f(O_{k′+1} | E(k′))`, the term of the last block of the
partition `{O₁, {s₁}, …, {s_{k′}}, O_{k′+1}}`; without it (5) is false. -/
theorem inequality_5 {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (f : Finset α → ℝ)
    (hmono : Monotone f) (hπ : IsWeakSubmodularOrder f π) (S T : Finset α) :
    f T ≤ f (T ∪ S) ∧
      f (T ∪ S) ≤ f S + ∑ j ∈ Finset.range (S.card + 1),
        marginal f (gapSet π S T j) (prefixSet π S j) := by sorry

end SubmodOrder
