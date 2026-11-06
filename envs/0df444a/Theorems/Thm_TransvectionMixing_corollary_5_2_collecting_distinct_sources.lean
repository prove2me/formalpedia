-- Prove2me | Theorems.Thm_TransvectionMixing_corollary_5_2_collecting_distinct_sources
-- name    : TransvectionMixing.corollary_5_2_collecting_distinct_sources
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:05.866395+00:00
-- url     : https://prove2.me/theorems/19cad660-45a8-435b-8e14-db87a85c2e49
-- title:
--   Corollary 5.2 — collecting distinct sources within $\lceil\mu+\sqrt{2\mu vL}+vL\rceil$ steps
-- statement:
--   1. Let $S,R\subseteq[n]$ be disjoint nonempty source and target sets, $1\le s\le|S|$ an integer and $L>0$. A uniformly random skeleton of length at least $\lceil\mu+\sqrt{2\mu vL}+vL\rceil$ contains updates from at least $s$ distinct rows of $S$ into $R$, except with probability at most $e^{-L}$, where
--   $$
--   \mu=\frac{n(n-1)}{|R|}\log\frac{|S|+1/2}{|S|-s+1/2},\qquad v=\frac{n(n-1)}{|R|(|S|-s+1)} .
--   $$
--   The receiving rows need not be distinct.
--   2. Fix $p$ consecutive phases, each with one or more such requirements $(S,R,s)$, $N$ requirements in all (row sets may overlap). Let $\mu_a$ and $v_a$ be the largest $\mu$ and $v$ among phase $a$'s requirements and run phase $a$ for $\lceil\mu_a+\sqrt{2\mu_av_aL}+v_aL\rceil$ independent uniform transvections. All $N$ requirements are met within their phases except with probability at most $Ne^{-L}$, and the total number of steps is at most
--   $$
--   \sum_{a=1}^p\mu_a+\sqrt{2L\Bigl(\sum_a\mu_a\Bigr)\Bigl(\sum_av_a\Bigr)}+L\sum_av_a+p .
--   $$
--
--   These estimates size every collection phase of the section constructions.
--
--   **Formalization Note** Requirement $i$ is a triple $(S,R,s)$ assigned to phase $\mathrm{ph}(i)$, every phase having at least one requirement; the phases are independent uniform skeletons of the prescribed lengths.
--
--   Differences from the source:
--   - encoding: p consecutive phases of one random skeleton → a tuple of independent uniform skeletons, one per phase, of the prescribed lengths; reason: the concatenation of independent uniform skeletons is a uniform skeleton; same probabilities
--   - encoding: µ_a, v_a the largest µ, v among phase a’s requirements → suprema over the (nonempty) set of requirements assigned to phase a; reason: finite nonempty supremum is the maximum
--   - encoding: a random skeleton of length at least ⌈µ + √(2µvL) + vL⌉ → every T : ℕ with ⌈µ + √(2µvL) + vL⌉₊ ≤ T; reason: same lengths
--   - encoding: laws of the walk over uniform skeletons and uniform coefficients → normalized counts (`prob`, `skelLaw`, `entryLaw`, `piS`) over finite types; reason: Lean convention for finite uniform probability; same values
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Corollary 5.2, pp.17–18

import Mathlib
import Definitions.Def_TransvectionMixing_walkMat
import Definitions.Def_TransvectionMixing_HasDisjointPaths

namespace TransvectionMixing

/-- **Corollary 5.2** (collecting distinct sources) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §5.1.2, pp.17–18).

1. Let `S, R ⊆ [n]` be disjoint nonempty source and target sets, `1 ≤ s ≤ |S|` an integer and
   `L > 0`. A random skeleton of length at least `⌈µ + √(2µvL) + vL⌉` contains updates from at
   least `s` distinct rows of `S` into `R` (receiving rows need not be distinct), except with
   probability at most `e^{−L}`, where `µ = (n(n−1)/|R|) log((|S| + 1/2)/(|S| − s + 1/2))`
   and `v = n(n−1)/(|R|(|S| − s + 1))`.
2. Fix `p` consecutive phases, each with one or more such requirements `(S, R, s)`, `N`
   requirements in all (row sets may overlap). Let `µ_a`, `v_a` be the largest `µ`, `v` among
   phase `a`'s requirements, and run phase `a` for `⌈µ_a + √(2µ_a v_a L) + v_a L⌉` independent
   uniform transvections. All `N` requirements are met within their phases except with
   probability at most `Ne^{−L}`, and the total number of steps is at most
   `∑µ_a + √(2L(∑µ_a)(∑v_a)) + L∑v_a + p`.

**Formalization Note** Requirement `i` is `req i = (S, R, s)` assigned to phase `ph i`; every
phase has a requirement (`ph` surjective). The phases are independent uniform skeletons of the
prescribed lengths (their concatenation is a uniform skeleton). -/
theorem corollary_5_2_collecting_distinct_sources (n : ℕ) :
    (∀ S R : Finset (Fin n), Disjoint S R → S.Nonempty → R.Nonempty → ∀ s : ℕ, 1 ≤ s →
        s ≤ S.card → ∀ L : ℝ, 0 < L → ∀ T : ℕ,
        ⌈collectMu n S R s + Real.sqrt (2 * collectMu n S R s * collectV n S R s * L)
            + collectV n S R s * L⌉₊ ≤ T →
        prob (fun σ : Skel n T => ¬ Collects σ S R s) ≤ Real.exp (-L)) ∧
      (∀ (p N : ℕ) (req : Fin N → Finset (Fin n) × Finset (Fin n) × ℕ) (ph : Fin N → Fin p),
        (∀ i, Disjoint (req i).1 (req i).2.1 ∧ (req i).1.Nonempty ∧ (req i).2.1.Nonempty ∧
          1 ≤ (req i).2.2 ∧ (req i).2.2 ≤ (req i).1.card) →
        Function.Surjective ph → ∀ L : ℝ, 0 < L →
        let μ : Fin p → ℝ := fun a =>
          ⨆ i : {i : Fin N // ph i = a}, collectMu n (req i).1 (req i).2.1 (req i).2.2
        let v : Fin p → ℝ := fun a =>
          ⨆ i : {i : Fin N // ph i = a}, collectV n (req i).1 (req i).2.1 (req i).2.2
        let ℓ : Fin p → ℕ := fun a =>
          ⌈μ a + Real.sqrt (2 * μ a * v a * L) + v a * L⌉₊
        prob (fun ω : (a : Fin p) → Skel n (ℓ a) =>
            ∃ i, ¬ Collects (ω (ph i)) (req i).1 (req i).2.1 (req i).2.2) ≤ N * Real.exp (-L) ∧
          ((∑ a, ℓ a : ℕ) : ℝ) ≤ ∑ a, μ a + Real.sqrt (2 * L * (∑ a, μ a) * (∑ a, v a))
            + L * ∑ a, v a + p) := by sorry

end TransvectionMixing
