-- Prove2me | Theorems.Thm_UncrowdedColoring_lemma_4_10
-- name    : UncrowdedColoring.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:17:17.738146+00:00
-- url     : https://prove2.me/theorems/a0a39462-0723-453b-9db1-ee7342da785c
-- title:
--   Lemma 4.10 (corrected: $|L(v)|=\lceil q_i\rceil$) — deterministic properties of a nibble step
-- statement:
--   Fix $k\ge 2$ and $0<\varepsilon<1$, the standing assumptions of §4, with $d\ge d_0(k,\varepsilon)$.
--   Let $(L,F)$ satisfy $P(i)$ with $i\in[s-1]$, and let $(\psi,\tilde L,\tilde F)$ be the output of Algorithm 4.1 for any outcome of the trials and any trimming. Then
--
--   1. $\psi$ is $(L,F)$-compatible;
--   2. for every $(\tilde L,\tilde F)$-compatible partial color assignment $\tilde\psi$ for $\tilde U$, $\psi\cup\tilde\psi$ is $(L,F)$-compatible;
--   3. $\bigcup_{c\in\tilde L(\tilde U)}\tilde F_c$ is rank-$k$ and uncrowded;
--   4. for every $c\ne c'$ in $\tilde L(\tilde U)$, $f\in E(\tilde F_c)$, $f'\in E(\tilde F_{c'})$, either $f=f'$ with $|f|=|f'|=k$, or $|f\cap f'|\le 1$.
--
--   These give (R1), (R3) and (Q1) of Lemma 4.7 with certainty. $P(i)$ is the corrected property of Definition 4.5, with $|L(v)|=\lceil q_i\rceil$.
--
--   Differences from the source:
--   - correction: (Q2) of Definition 4.5 prints |L(v)| = q_i with q_i real → |L(v)| = ⌈q_i⌉ in SatisfiesP; reason: the printed condition is false for nonempty instances: k = 2, ε = 1/2, integer d ≥ 2 give q_1 = (3/2)d/log d, irrational since log d is transcendental, so no finite list has size q_1; p.14 warns that ceilings are omitted
--   - generalization: d ≥ d_0 with d_0 ∈ ℕ, d read as an integer → d : ℝ with (d₀ : ℝ) ≤ d; reason: §7, eq. (81), p.53 applies the results at a non-integer d; natural d is a cast
--   - encoding: a finite set U with L, F, ψ defined on it → U : Finset V inside V : Type; L and F total and read on U; ψ : V → Option ℕ; reason: a Lean convention: every finite set is such a U, and values off U are not read
--   - generalization: the output of Algorithm 4.1 → every T : TrialSpace U L, including null outcomes with a color off the list; reason: ψ only reads colors in L′(v), so the proof is unchanged; every actual output is such a T
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Lemma 4.10, p.25

import Mathlib
import Definitions.Def_UncrowdedColoring_IsCompatible
import Definitions.Def_UncrowdedColoring_SatisfiesP
import Definitions.Def_UncrowdedColoring_nibblePsi

open scoped Classical

namespace UncrowdedColoring

/-- **Lemma 4.10**, p.25: the deterministic properties of the output of Algorithm 4.1.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Lemma 4.10, p.25.

**Formalization Note.** The lemma holds for every outcome `T` of the trials and every trimming `L̃`
(Step (6) trims "arbitrarily"). `k ≥ 2`, `0 < ε < 1`, and `d ≥ d₀(k, ε)` are the standing assumptions
of §4 (p.16). The trimming target is `⌈q_{i+1}⌉` and the input satisfies the corrected `P(i)` (see
`SatisfiesP`). -/
theorem lemma_4_10 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ d₀ : ℕ, ∀ d : ℝ, (d₀ : ℝ) ≤ d →
      ∀ (V : Type) (U : Finset V) (L : V → Finset ℕ) (F : ℕ → Finset (Finset V)) (i : ℕ),
        i + 1 ≤ numSteps ε d → IsRestrictionFamily U L F → SatisfiesP k ε d i U L F →
        ∀ (T : TrialSpace U L) (Lt : V → Finset ℕ),
          IsTrimming (uTilde F T) (keptColours F T) Lt (qSeq k ε d (i + 1)) →
          -- (1)
          IsCompatible U L F (nibblePsi F T) ∧
          -- (2)
          (∀ ψt : V → Option ℕ, IsPartialAssignment (uTilde F T) ψt →
            IsCompatible (uTilde F T) Lt (fTilde k F T Lt) ψt →
            IsCompatible U L F (unionAssign (nibblePsi F T) ψt)) ∧
          -- (3)
          IsRank (unionHypergraph (uTilde F T) Lt (fTilde k F T Lt)) k ∧
          IsUncrowded (unionHypergraph (uTilde F T) Lt (fTilde k F T Lt)) ∧
          -- (4)
          ∀ c ∈ colours (uTilde F T) Lt, ∀ c' ∈ colours (uTilde F T) Lt, c ≠ c' →
            ∀ f ∈ fTilde k F T Lt c, ∀ f' ∈ fTilde k F T Lt c',
              (f = f' ∧ f.card = k) ∨ (f ∩ f').card ≤ 1 := by sorry

end UncrowdedColoring
