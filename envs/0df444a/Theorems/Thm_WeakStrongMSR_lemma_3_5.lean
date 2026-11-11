-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_5
-- name    : WeakStrongMSR.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:30.543716+00:00
-- url     : https://prove2.me/theorems/b1ad06ce-268f-4694-b368-44b9f61eb3ce
-- title:
--   Lemma 3.5 — the median estimate: $d(s,x)\le\mathrm{md}(x,s)\le d(s,x)+2r_s$ off $E_s$
-- statement:
--   Let $d$ be a metric, $C$ a corruption set and $\tilde d$ the weak distances for some adversary. Let $S$ be a strong set, $s\in S$, and $W\subseteq S\setminus\{s\}$ a nonempty witness set with radius $r_s=\max_{w\in W}d(s,w)$. Let $\mathrm{md}(\cdot,s)$ be the estimate of Eq. (3) and $E_s$ the set of points corrupt for $W$.
--
--   1. Every $x\notin E_s$ satisfies
--   $$d(s,x)\le \mathrm{md}(x,s)\le d(s,x)+2r_s.$$
--   2. For every $R$, $\{x:\mathrm{md}(x,s)\le R\}\setminus E_s\subseteq B(s,R)$. In particular $A(s,R)\setminus E_s\subseteq B(s,R)$ for every candidate at $s$.
--   3. If every set of $|W|$ points has fewer than $|W|/2$ corrupt points (the event of Lemma 3.3), then $|E_s|<|W|/2$.
--
--   This is the basic link between weak-distance estimates and true distances.
--
--   **Formalization Note** The median is the lower median.
--
--   Differences from the source:
--   - generalization: a sampled centre s with its witness set W_s (the h nearest points of S \ {s}) → any s ∈ S and any nonempty W ⊆ S \ {s}; reason: covers every adaptively chosen witness set, in particular the paper's
--   - reading: the median of h (even) values → the lower median; reason: the paper does not fix which middle value; the statement holds for it
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.5, p.11 (PDF 12)

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.5** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.11, PDF p.12).
"For every sampled centre s with a witness set and every x ∉ E_s, d(s, x) ≤ md(x, s) ≤ d(s, x) + 2r_s.
(5) Consequently A(s, R) \ E_s ⊆ B(s, R) for every candidate at s. On the event of Lemma 3.3, we
also have |E_s| < h/2."

Let `d` be a metric, `C` a corruption set and `adv` an adversary, with weak table
`w = weakDist d C adv`. Let `S` be a strong set, `s ∈ S`, and `W ⊆ S ∖ {s}` a nonempty witness
set with radius `r_s = max_{v ∈ W} d(s, v)`, and let `md(·, s)` be the estimate (3). Then
1. every point `x` not corrupt for `W` satisfies `d(s, x) ≤ md(x, s) ≤ d(s, x) + 2r_s`;
2. for every `R`, `{x : md(x, s) ≤ R} ∖ E_s ⊆ B(s, R)` (so `A(s, R) ∖ E_s ⊆ B(s, R)` for every
   candidate at `s`, whose set lies in this sublevel set);
3. if every set of `|W|` points has fewer than `|W|/2` corrupt points (the event of Lemma 3.3),
   then `|E_s| < |W|/2`.

**Formalization Note.** The witness set is arbitrary (any nonempty subset of `S ∖ {s}`), so the
lemma applies to every adaptively chosen witness set; the median is the lower median. -/
theorem lemma_3_5 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsMetric d)
    (C : Finset (Sym2 (Fin n))) (adv : Adversary n) (S W : Finset (Fin n)) (s : Fin n)
    (hs : s ∈ S) (hWS : W ⊆ S.erase s) (hW : W.Nonempty) :
    (∀ x : Fin n, ¬ IsCorruptFor C W x →
      d s x ≤ mdEst d (weakDist d C adv) S s W x ∧
        mdEst d (weakDist d C adv) S s W x ≤ d s x + 2 * witnessRadius d s W) ∧
    (∀ R : ℝ, (Finset.univ.filter (fun x => mdEst d (weakDist d C adv) S s W x ≤ R)) \
        corruptSet C W ⊆ (⟨s, R⟩ : MinSumRadiiPTAS.Main.Ball n).pts d) ∧
    ((∀ W' : Finset (Fin n), W'.card = W.card →
        ((corruptSet C W').card : ℝ) < (W.card : ℝ) / 2) →
      ((corruptSet C W).card : ℝ) < (W.card : ℝ) / 2) := by sorry

end WeakStrongMSR
