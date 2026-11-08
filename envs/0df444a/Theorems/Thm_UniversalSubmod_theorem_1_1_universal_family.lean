-- Prove2me | Theorems.Thm_UniversalSubmod_theorem_1_1_universal_family
-- name    : UniversalSubmod.theorem_1_1_universal_family
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:51:41.743222+00:00
-- url     : https://prove2.me/theorems/49b4145a-33b1-4614-a6d0-8a9fbdaee9be
-- title:
--   Theorem 1.1 — a family of $n^{O(\varepsilon^{-2}\log(1/\varepsilon))}$ sets contains a $(1/4-\varepsilon)$-approximate maximizer of every nonnegative submodular function
-- statement:
--   There is an absolute constant $C$ such that the following holds. For every $\varepsilon\in(0,1/4)$ and every integer $n\ge2$ there is a family of sets $\mathcal F_{n,\varepsilon}\subsetneq 2^{[n]}$ with
--   $$
--   |\mathcal F_{n,\varepsilon}|\ \le\ n^{\,C\varepsilon^{-2}\log(1/\varepsilon)}
--   $$
--   such that for every nonnegative submodular function $f:2^{[n]}\to\mathbb R$,
--   $$
--   \max_{S\in\mathcal F_{n,\varepsilon}}f(S)\ \ge\ \Big(\frac14-\varepsilon\Big)\max_{S\subseteq[n]}f(S).
--   $$
--   The family depends only on $n$ and $\varepsilon$, not on $f$. This is the paper's statement "$|\mathcal F_{n,\varepsilon}|=n^{O(1/\varepsilon^2\log(1/\varepsilon))}$" with the $O(\cdot)$ made explicit.
--
--   Querying $f$ on $\mathcal F_{n,\varepsilon}$ is a deterministic non-adaptive algorithm with approximation factor $1/4-\varepsilon$ using polynomially many queries for fixed $\varepsilon$; a factor $1/4+\varepsilon$ requires exponentially large families, so the factor is optimal up to $\varepsilon$.
--
--   **Formalization Note** The $O(\cdot)$ is one constant $C$ quantified before $\varepsilon$ and $n$; the power is the real power $n^{C\varepsilon^{-2}\log(1/\varepsilon)}$. Subsets are `Finset (Fin n)`, and the strict inclusion is `F ≠ Finset.univ`.
--
--   Differences from the source:
--   - reading: $\mathcal F_{n,\varepsilon}\subset2^{[n]}$ → `F ≠ Finset.univ` (strict inclusion); reason: the stronger of the two readings of $\subset$; it holds because $2^{[n]}\setminus\{\emptyset\}$ also works when $n\ge2$
--   - encoding: $|\mathcal F_{n,\varepsilon}|=n^{O(1/\varepsilon^2\log(1/\varepsilon))}$ → $\exists C$ before $\varepsilon$ and $n$ with $|\mathcal F|\le n^{C\varepsilon^{-2}\log(1/\varepsilon)}$ (real power); reason: the $O(\cdot)$ as an upper bound with one absolute constant; the proof's bound on p.14 meets it
--   - encoding: $\max_{S\in\mathcal F}f(S)\ge(1/4-\varepsilon)\max_Sf(S)$ → $\exists S\in\mathcal F$ with $(1/4-\varepsilon)\,\mathrm{OPT}(f)\le f(S)$; reason: equivalent for a finite family (and the maximum presupposes $\mathcal F\neq\emptyset$)
--   - encoding: the ground set $[n]$, subsets $S\subseteq[n]$, $f:2^{[n]}\to\mathbb R_{\ge0}$ → `Fin n`, `Finset (Fin n)`, a real-valued `f` with $f(S)\ge0$ for all $S$; reason: a relabelling of $[n]$; the same functions
--   - encoding: $\max_{S\subseteq[n]} f(S)$ → the published `OPT f` (a maximum over the nonempty finite family of all subsets); reason: the same number
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), Theorem 1.1, p.3 (proof pp.13–14)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT

namespace UniversalSubmod

open NonmonotoneSubmod.Shared

/-- **Theorem 1.1** (optimal universal families; Adamczyk, Ueltzen, Vondrák, *Optimal universal sets
for submodular functions*, manuscript of November 3, 2026, Theorem 1.1, p.3; proof pp.13–14). For
every `ε ∈ (0, 1/4)` and every `n ≥ 2`, there is a family of sets `F_{n,ε} ⊂ 2^[n]`,
`|F_{n,ε}| = n^{O(1/ε² log(1/ε))}`, such that for every nonnegative submodular function
`f : 2^[n] → ℝ`, `max_{S ∈ F_{n,ε}} f(S) ≥ (1/4 − ε) max_{S⊆[n]} f(S)`.

**Formalization Note.** The `O(·)` is one absolute constant `C`, chosen before `ε` and `n`:
`|F| ≤ n^{C ε⁻² log(1/ε)}` (real power). The family is chosen before `f`. `⊂` is read as strict
inclusion, `F ≠ 2^[n]`. `max_{S∈F} f(S) ≥ …` is `∃ S ∈ F` with `f(S) ≥ …`. `[n]` is `Fin n`; `f` is
real valued with `f ≥ 0`; `max_{S⊆[n]} f(S)` is the published `OPT`. -/
theorem theorem_1_1_universal_family :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∀ n : ℕ, 2 ≤ n →
      ∃ F : Finset (Finset (Fin n)),
        F ≠ Finset.univ ∧
        (F.card : ℝ) ≤ (n : ℝ) ^ (C * (1 / ε ^ 2) * Real.log (1 / ε)) ∧
        ∀ f : Finset (Fin n) → ℝ, (∀ S, 0 ≤ f S) → Submodular f →
          ∃ S ∈ F, (1 / 4 - ε) * OPT f ≤ f S := by sorry

end UniversalSubmod
