-- Prove2me | Theorems.Thm_TransvectionMixing_proposition_6_1_number_of_requested_entries
-- name    : TransvectionMixing.proposition_6_1_number_of_requested_entries
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:27.414541+00:00
-- url     : https://prove2.me/theorems/8316cee4-a0a2-4a90-a5a9-13c56b38a771
-- title:
--   Proposition 6.1 — support lower bound: $\|\mathcal L_X(X_t|_{\mathcal S})-\pi_{\mathcal S}\|_{TV}\ge 1-2q^{1-|\mathcal S|}[n(n-1)q]^t$
-- statement:
--   Let $n\ge 2$ and $q=|\mathbb F_q|$. For every nonempty $\mathcal S\subseteq[n]\times[n]$, initial state $X$ and integer $t\ge 0$,
--   $$
--   \bigl\|\mathcal L_X(X_t|_{\mathcal S})-\pi_{\mathcal S}\bigr\|_{TV}\ \ge\ 1-2q^{1-|\mathcal S|}\,[n(n-1)q]^t .
--   $$
--   For every skeleton $\sigma$,
--   $$
--   d^\sigma_{\mathcal S}(X)\ \ge\ 1-2q^{1-|\mathcal S|+|\sigma|}.
--   $$
--   For full-column sets $\mathcal S=[n]\times C$, the factor $2q^{1-|\mathcal S|}$ in both bounds is replaced by $1/|\mathrm{supp}\,\pi_{\mathcal S}|$.
--
--   This is the "too few possible outputs" obstruction behind the $|\mathcal S|$ term of the lower bound.
--
--   **Formalization Note** Integer powers are `zpow`; $|\mathrm{supp}\,\pi_{\mathcal S}|$ is the number of points of positive $\pi_{\mathcal S}$-mass.
--
--   Differences from the source:
--   - encoding: the walk on n rows (the paper's results take n ≥ 2 implicitly: a step needs two distinct rows) → hypothesis 2 ≤ n; reason: excludes only n ≤ 1, where no skeleton of positive length exists
--   - encoding: full-column sets → 𝒮 = [n] × C for a set of columns C; reason: definition of a full-column set
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
--   - encoding: ‖·‖_TV → the published `MarkovMixing.tvDist` (max over events of |μ(A) − ν(A)|); reason: equals ½∑|μ − ν| on probability vectors; same values
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Proposition 6.1, eqs. (43)–(44), pp.33–34

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_TransvectionMixing_dS

namespace TransvectionMixing

/-- **Proposition 6.1** (the number of requested entries) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §6.1, pp.33–34). Write
`q = |𝔽_q|`. For every nonempty `𝒮 ⊆ [n] × [n]`, initial state `X`, and integer `t ≥ 0`,
`‖ℒ_X(X_t|_𝒮) − π_𝒮‖_TV ≥ 1 − 2q^{1−|𝒮|}[n(n − 1)q]^t` (eq. (43)). For every skeleton `σ`,
`d^σ_𝒮(X) ≥ 1 − 2q^{1−|𝒮|+|σ|}` (eq. (44)). For full-column sets `𝒮 = [n] × C`, `2q^{1−|𝒮|}` is
replaced in both bounds by `1/|supp π_𝒮|`.

**Formalization Note** `n ≥ 2` (the walk needs two distinct rows). Powers with integer
exponents are `zpow`. -/
theorem proposition_6_1_number_of_requested_entries (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin n × Fin n)) (hS : S.Nonempty)
    (X : Matrix.SpecialLinearGroup (Fin n) F) :
    (∀ t : ℕ, 1 - 2 * (Fintype.card F : ℝ) ^ ((1 : ℤ) - S.card)
        * ((n : ℝ) * ((n : ℝ) - 1) * Fintype.card F) ^ t
        ≤ MarkovMixing.tvDist (entryLaw F t X S) (piS F S)) ∧
      (∀ (t : ℕ) (σ : Skel n t),
        1 - 2 * (Fintype.card F : ℝ) ^ ((1 : ℤ) - S.card + t) ≤ dSigma F σ X S) ∧
      (∀ C : Finset (Fin n), S = (Finset.univ : Finset (Fin n)) ×ˢ C →
        (∀ t : ℕ, 1 - 1 / (((Finset.univ.filter (fun y => 0 < piS F S y)).card : ℕ) : ℝ)
            * ((n : ℝ) * ((n : ℝ) - 1) * Fintype.card F) ^ t
            ≤ MarkovMixing.tvDist (entryLaw F t X S) (piS F S)) ∧
        (∀ (t : ℕ) (σ : Skel n t),
          1 - (Fintype.card F : ℝ) ^ t
            / (((Finset.univ.filter (fun y => 0 < piS F S y)).card : ℕ) : ℝ)
            ≤ dSigma F σ X S)) := by sorry

end TransvectionMixing
