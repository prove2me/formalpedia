-- Prove2me | Theorems.Thm_UniversalSubmod_lemma_2_1
-- name    : UniversalSubmod.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:51:43.529313+00:00
-- url     : https://prove2.me/theorems/96327bb0-b5c2-4cb9-b971-e8836c2bcf65
-- title:
--   Lemma 2.1 — independent sampling: $\mathbb E[f(R_p)]\ge p(1-p)\max f$
-- statement:
--   Let $f:2^{[n]}\to\mathbb R_{\ge0}$ be nonnegative submodular and let $p\in[0,1]$. If $R_p\subseteq[n]$ contains each element independently with probability $p$, then
--   $$
--   \mathbb E[f(R_p)]\ \ge\ p(1-p)\max_{S\subseteq[n]}f(S).
--   $$
--   In the notation of the multilinear extension this reads $F(p\mathbf 1)\ge p(1-p)\max_S f(S)$; $p=1/2$ is the $1/4$-approximation of a uniformly random set (Feige, Mirrokni, Vondrák).
--
--   This bound is used conditionally on the common Gaussian component in the proof of Theorem 2.4.
--
--   **Formalization Note** $\mathbb E[f(R_p)]$ is the published multilinear extension at the constant vector, $F(p\mathbf 1)=\sum_{S}f(S)\,p^{|S|}(1-p)^{n-|S|}$.
--
--   Differences from the source:
--   - encoding: $\mathbb E[f(R_p)]$ → `F f (fun _ => p)`, the multilinear extension at $p\mathbf 1$; reason: the definition of that expectation; the paper writes it so on p.6
--   - encoding: the ground set $[n]$, subsets $S\subseteq[n]$, $f:2^{[n]}\to\mathbb R_{\ge0}$ → `Fin n`, `Finset (Fin n)`, a real-valued `f` with $f(S)\ge0$ for all $S$; reason: a relabelling of $[n]$; the same functions
--   - encoding: $\max_{S\subseteq[n]} f(S)$ → the published `OPT f` (a maximum over the nonempty finite family of all subsets); reason: the same number
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), Lemma 2.1, p.4 (proof p.19)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace UniversalSubmod

open NonmonotoneSubmod.Shared

/-- **Lemma 2.1** (independent sampling; Adamczyk, Ueltzen, Vondrák, *Optimal universal sets for
submodular functions*, manuscript of November 3, 2026, Lemma 2.1, p.4; proof p.19). If `R_p ⊆ [n]`
contains each element independently with probability `p ∈ [0,1]`, then for every nonnegative
submodular `f : 2^[n] → ℝ≥0`, `E[f(R_p)] ≥ p(1 − p) max_{S⊆[n]} f(S)`.

**Formalization Note.** `E[f(R_p)]` is the multilinear extension at the constant vector,
`F(p1) = ∑_S f(S) p^{|S|} (1 − p)^{n − |S|}` (the published `NonmonotoneSubmod.Shared.F`), as the
paper itself writes it on p.6. -/
theorem lemma_2_1 {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (1 - p) * OPT f ≤ F f (fun _ => p) := by sorry

end UniversalSubmod
