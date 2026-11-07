-- Prove2me | Theorems.Thm_SteinerAPX_lemma_16
-- name    : SteinerAPX.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:02.793419+00:00
-- url     : https://prove2.me/theorems/2c7a1e44-34fd-47f7-a03d-182797f1562c
-- title:
--   Lemma 16 — a polynomial-time gap reduction from 3DM-3 to Euclidean Steiner Tree with $n=\Theta(m)$ terminals in $\mathbb R^{O(n)}$
-- statement:
--   For every $\delta\in(0,1)$ there are constants $\beta>0$ and a rational $\rho\in(0,1/100]$ such that the following holds. Given a 3DM-3 instance $H$ of size $m$, one can construct in polynomial time $n=\Theta(m)$ terminals $P_\rho\subseteq\mathbb R^{O(n)}$, namely the sampled terminals of the orthogonal routing of $H$ (with coordinates renumbered), and a rational threshold $\tau>0$ with
--   $$
--   \nu(H)=r\ \Longrightarrow\ \mathrm{OPT}(P_\rho)\le\tau,\qquad
--   \nu(H)\le(1-\delta)r\ \Longrightarrow\ \mathrm{OPT}(P_\rho)\ge(1+\beta)\tau .
--   $$
--   Here $\Theta(m)$ and $O(n)$ mean: constants $c_1,c_2,c_3>0$ with $c_1m\le n\le c_2m$ and dimension $k\le c_3n$.
--
--   Combined with Lemma 4, this shows that Euclidean Steiner Tree is APX-hard already in $O(n)$ dimensions.
--
--   **Formalization Note** The machine is a Mathlib `TM2ComputableInPolyTime` machine with a finite alphabet, from raw 3DM codes to raw instances.
--
--   Differences from the source:
--   - generalization: δ the constant of Lemma 4 → every δ ∈ (0, 1), with β depending on δ; reason: the proof works for any δ ∈ (0, 1); taking Lemma 4's δ recovers the source's statement
--   - encoding: terminals Pρ ⊆ R^O(n) and a threshold τ → the rational sampled terminals of the orthogonal routing with one fixed port assignment (orthDir), carried to ℝᵏ by a renumbering of coordinates, and a rational threshold τ > 0; reason: every coordinate on this route is rational for rational ρ; the paper's threshold L + (4/3)|U| − ∆r is positive and may be replaced by a rational one at the cost of part of β; the paper constructs the routing with some assignment, and fixing one makes the existential claim more specific, not weaker
--   - reading: Consequently, Euclidean Steiner Tree is APX-hard already in O(n) dimensions → not stated separately; reason: it is the same constant gap in dimension O(n), stated in the main clauses; composed with Lemma 4 it is the APX-hardness sense of Theorem 1
--   - encoding: given an instance H of 3DM-3 → every valid raw code (r ≥ 1, coordinates < r, no repeated triple) of a 3DM-3 instance; reason: a machine reads codes; r ≥ 1 excludes only the empty instance, which the paper never considers
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 16, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_SteinerAPX_RawTerminals
import Definitions.Def_SteinerAPX_samples
import Definitions.Def_SteinerAPX_orthogonalRouting

namespace SteinerAPX

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity Inst3DM CableLayout

/-- **Lemma 16 (constant gap in linear dimension).** S. Bartlmae, *Inapproximability of Euclidean
Steiner Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 16, p.21 (PDF p.23):
"There are constants β > 0 and ρ > 0 such that the following holds. Given an instance H of 3DM-3,
one can construct in polynomial time n = Θ(m) terminals Pρ ⊆ RO(n) and a threshold τ with
ν(H) = r =⇒ OPT(Pρ) ≤ τ, ν(H) ≤ (1 − δ)r =⇒ OPT(Pρ) ≥ (1 + β)τ. Consequently, Euclidean Steiner
Tree is APX-hard already in O(n) dimensions."

For every `δ ∈ (0, 1)` (the constant of Lemma 4) there are `β > 0`, a rational `0 < ρ ≤ 1/100`,
constants `c₁, c₂, c₃ > 0` and a polynomial-time machine mapping raw 3DM codes to raw instances
`(k, ps, τ)` such that for every valid 3DM-3 instance `H` of size `m`: the output is valid, has
`c₁m ≤ n ≤ c₂m` terminals in dimension `k ≤ c₃n`, a threshold `τ > 0`, and its terminal set is
`Pρ` of the orthogonal routing of `H`, carried to `ℝᵏ` by a relabelling of coordinates; and
`ν(H) = r ⇒ OPT ≤ τ`, `ν(H) ≤ (1 − δ)r ⇒ OPT ≥ (1 + β)τ`.

**Formalization Note** `δ` is a parameter (Lemma 4 supplies one value); `β` depends on it. The
"Consequently" sentence is the same gap and is not stated separately. The threshold is rational and
is not tied to the irrational `L + (4/3)|U| − ∆r` of the proof. The terminals are pinned to the
sampled orthogonal routing ("terminals Pρ") with the fixed port assignment `orthDir`; the
coordinates `OrthIndex H` (`D = m + |U| + 3`) are renumbered as `Fin k` by some bijection. The machine is a Mathlib `TM2ComputableInPolyTime` with a
finite alphabet, from `Raw3DM.bits` to `rawInstanceBits`. -/
theorem lemma_16 :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℚ, 0 < ρ ∧ ρ ≤ 1 / 100 ∧
    ∃ c₁ c₂ c₃ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
    ∃ construct : Raw3DM → RawInstance,
    ∃ comp : Turing.TM2ComputableInPolyTime Raw3DM.bits rawInstanceBits construct,
      MachineFiniteAlphabet.FiniteAlphabet comp.tm ∧
      ∀ (R : Raw3DM) (hR : R.Valid), (R.toInst hR).IsThreeDM3 →
        (construct R).1.Valid ∧
        c₁ * ((R.toInst hR).size : ℝ) ≤ ((construct R).1.n : ℝ) ∧
        ((construct R).1.n : ℝ) ≤ c₂ * ((R.toInst hR).size : ℝ) ∧
        ((construct R).1.k : ℝ) ≤ c₃ * ((construct R).1.n : ℝ) ∧
        (0 : ℝ) < ((construct R).2 : ℝ) ∧
        (∃ eqv : OrthIndex (R.toInst hR) ≃ Fin (construct R).1.1,
          (construct R).1.terminals =
            (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eqv) ''
              samples (orthogonalRouting (R.toInst hR)) (ρ : ℝ)) ∧
        ((R.toInst hR).nu = (R.toInst hR).r →
          opt (construct R).1.terminals ≤ ((construct R).2 : ℝ)) ∧
        (((R.toInst hR).nu : ℝ) ≤ (1 - δ) * ((R.toInst hR).r : ℝ) →
          (1 + β) * ((construct R).2 : ℝ) ≤ opt (construct R).1.terminals) := by sorry

end SteinerAPX
