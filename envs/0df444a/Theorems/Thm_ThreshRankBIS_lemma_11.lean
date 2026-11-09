-- Prove2me | Theorems.Thm_ThreshRankBIS_lemma_11
-- name    : ThreshRankBIS.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:06:25.295813+00:00
-- url     : https://prove2.me/theorems/0098b7c5-ecc2-4882-b60c-0138f5ac6925
-- title:
--   Lemma 11 — refinement and weighted reconstruction, $q^{-w}\sum\lambda^{|B|}\le q^{-\theta t}$
-- statement:
--   For every fixed $\lambda_0>0$ there is a constant $0<\theta\le1/16$ such that the following holds for every simple $d$-regular bipartite graph $G$ with $|X|=|Y|=n$, $d\ge1$. Let $t\ge1$ and $h\ge0$ be integers, let $F_0\subseteq Y$, and put $\psi=\theta d/4$. There is a family of pairs $(S,F)$ with $S\subseteq X$, $F\subseteq Y$ and $|S|-|F|\le\theta t$ such that:
--
--   1. every closed $A$ of deficit $t$ with $F_0\subseteq N(A)$ and $|N(A)\setminus F_0|\le h$ satisfies $A\subseteq S$ and $F\subseteq N(A)$ for some pair;
--   2. each pair is decoded from $F_0$ and sets $H_X\subseteq X$, $H_Y\subseteq Y$ with $|H_X|\le h/\psi$ and $|H_Y|\le2t/\psi$;
--   3. for every pair, every $w$ and every $\lambda\ge\lambda_0$, with $q=1+\lambda$,
--   $$
--   q^{-w}\sum_{\substack{B\in H(w,t)\\ [B]\subseteq S,\ F\subseteq N(B)}}\lambda^{|B|}\le q^{-\theta t}. \tag{15}
--   $$
--
--   This is the graph-container step with hard-core weights: each container pair carries normalized weight $q^{-\theta t}$, while the number of pairs is controlled by the witness sizes in clause 2.
--
--   **Formalization Note** "Decoded from $F_0$, $H_X$, $H_Y$" is a decoding map $(F_0,H_X,H_Y)\mapsto(S,F)$ that depends on the graph only (it is chosen before $F_0$, $t$, $h$), and every pair of the family is its value at admissible $H_X$, $H_Y$.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
--   - reading: each pair is decoded from F₀ and sets H_X, H_Y → there is a map dec(F₀, H_X, H_Y) = (S, F), fixed once the graph is fixed (before F₀, t, h), such that every pair of the family is dec F₀ H_X H_Y for some H_X, H_Y with the size bounds; reason: the decoding formulas of the proof (p.14) depend only on G, ψ and (F₀, H_X, H_Y); this is the strongest reading of the clause
--   - generalization: the fugacity λ, rational where it is an algorithm input (p.3) → λ a real number with the same lower bound; reason: the statement is about the combinatorial weights only and holds for every real λ in the range; it specializes to rational λ
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 11, p.13, display (15)

import Mathlib
import Definitions.Def_ThreshRankBIS_mWeight
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Lemma 11 (Refinement and weighted reconstruction)**, p.13. For every fixed `λ_0 > 0` there
is a constant `0 < θ ≤ 1/16` such that the following holds for every `d`-regular bipartite `G`
(`d ≥ 1`). Let `t ≥ 1` and `h ≥ 0` be integers, let `F_0 ⊆ Y`, and put `ψ = θd/4`. Then there is
a family of pairs `(S, F)`, `S ⊆ X`, `F ⊆ Y`, `|S| − |F| ≤ θt`, such that
1. every closed `A` of deficit `t` with `F_0 ⊆ N(A)` and `|N(A) ∖ F_0| ≤ h` satisfies `A ⊆ S` and
   `F ⊆ N(A)` for some pair;
2. each pair is decoded from `F_0` and sets `H_X ⊆ X`, `H_Y ⊆ Y` with `|H_X| ≤ h/ψ` and
   `|H_Y| ≤ 2t/ψ`;
3. for every pair, every `w` and every `λ ≥ λ_0`,
   `q^{−w} ∑_{B ∈ H(w,t), [B] ⊆ S, F ⊆ N(B)} λ^{|B|} ≤ q^{−θt}` (display (15)).

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 11, p.13.

**Formalization Note.** "Decoded from `F_0`, `H_X`, `H_Y`" is a decoding map
`dec : (F_0, H_X, H_Y) ↦ (S, F)` fixed once the graph is fixed (before `F_0`, `t`, `h`), and every
pair of the family is `dec F_0 H_X H_Y` for admissible `H_X`, `H_Y`. Subsets of `X` and of `Y`
are both `Finset (Fin n)`. `λ` is real. `q^{−θt}` is a real power. -/
theorem lemma_11 (lam0 : ℝ) (hlam0 : 0 < lam0) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 16 ∧
      ∀ {n d : ℕ} (E : Fin n → Fin n → Bool), IsRegular E d → 1 ≤ d → 0 < n →
      ∃ dec : Finset (Fin n) → Finset (Fin n) → Finset (Fin n) →
          Finset (Fin n) × Finset (Fin n),
        ∀ (t h : ℕ), 1 ≤ t → ∀ F0 : Finset (Fin n),
        ∃ Pairs : Finset (Finset (Fin n) × Finset (Fin n)),
          (∀ p ∈ Pairs, (#p.1 : ℝ) - #p.2 ≤ θ * t) ∧
          (∀ A : Finset (Fin n), IsClosedLeft E A → deficit E A = t → F0 ⊆ nbhd E A →
            #(nbhd E A \ F0) ≤ h → ∃ p ∈ Pairs, A ⊆ p.1 ∧ p.2 ⊆ nbhd E A) ∧
          (∀ p ∈ Pairs, ∃ HX HY : Finset (Fin n),
            (#HX : ℝ) ≤ h / (θ * d / 4) ∧ (#HY : ℝ) ≤ 2 * t / (θ * d / 4) ∧
              dec F0 HX HY = p) ∧
          (∀ p ∈ Pairs, ∀ (w : ℕ) (lam : ℝ), lam0 ≤ lam →
            ((1 + lam) ^ w)⁻¹ *
                ∑ B ∈ (Hwt E w t).filter (fun B => closure E B ⊆ p.1 ∧ p.2 ⊆ nbhd E B),
                  lam ^ #B ≤
              (1 + lam) ^ (-(θ * t))) := by sorry

end ThreshRankBIS
