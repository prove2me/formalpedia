-- Prove2me | Theorems.Thm_SensLabelCover_DH_theorem_11_1
-- name    : SensLabelCover.DH.theorem_11_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:36:42.582743+00:00
-- url     : https://prove2.me/theorems/95513209-2a5c-4087-a026-8939655541b4
-- title:
--   Theorem 11.1 — for all $1<g\le\log^B n$, swap-closed left-predicate Label Cover families with $|U|=n$ on which every value-$1/g$ algorithm has sensitivity $\Omega(n^\delta)$
-- statement:
--   There are absolute constants $B,\delta,c,K>0$ and $n_{\min}\in\mathbb N$ such that for every integer $n\ge n_{\min}$ and every real $g$ with $1<g\le(\log n)^B$ there are a bipartite multigraph $G=(U,V,E)$ with $|U|=n$, nonempty finite alphabets $\Sigma_U,\Sigma_V$ and a swap-closed family $\mathcal I$ of left-predicate Label Cover instances on them with the following properties.
--   - **Sensitivity.** Every algorithm $A$, mapping instances to probability distributions over assignments with no computational restriction, with
--   $$\mathbb E_{\pi\sim A(I)}\big[\mathrm{val}_I(\pi)\big]\ge\frac1g\quad\text{for every satisfiable }I\in\mathcal I,$$
--   has a member $I\in\mathcal I$ and a projection swap or predicate swap $J$ of $I$ with $\mathrm{EMD}(A(I),A(J))\ge c\,n^\delta$; that is, $\mathrm{SwapSens}(A,\mathcal I)\ge c\,n^\delta$.
--   - **Size.** $|V|\le n(\log n)^K$, every left and every right degree is at most $K g^K$, $|\Sigma_V|\le Kg^K$ and $|\Sigma_U|\le\exp(Kg^K)$.
--
--   This is the paper's answer to its central question. Even when an algorithm only has to satisfy a $1/g$ fraction of the constraints on satisfiable instances, Label Cover forces polynomial sensitivity, with an exponent independent of $g$.
--
--   Differences from the source:
--   - reading: $\Omega(n^\delta)$, $\log^{O(1)}n$, $g^{O(1)}$, $\exp(g^{O(1)})$ → $c\,n^\delta$, $(\log n)^K$, $Kg^K$, $\exp(Kg^K)$ with absolute $c,K$ fixed before $n$ and $g$; reason: the proof (p. 62) says these mean an absolute constant times the specified power, uniformly even for $g$ close to $1$.
--   - encoding: "a swap-closed family of instances with $|U|=n$" → a fixed graph and fixed alphabets with a swap-closed set of $(P,F)$ on them; reason: the paper's family is the swap closure of instances on one graph (§11.4), and swaps never change graph or alphabets.
--   - encoding: "has sensitivity $\Omega(n^\delta)$" → for every algorithm with the guarantee, some member and some one swap have EMD $\ge c\,n^\delta$; reason: the family is finite, so this is $\mathrm{SwapSens}(A,\mathcal I)\ge c\,n^\delta$.
--   - encoding: vertex, edge and alphabet sets → `Fin n`, `Fin m`, `Fin e`, `Fin a`, `Fin b` with $a,b\ge1$; $\log$ → natural logarithm; reason: Lean convention. The alphabets are nonempty, and the base of the logarithm is absorbed by the existential $B$ and $K$.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 57 (PDF 60), Theorem 11.1 (formal version of Theorem 1.2); proof pp. 57–63

import Mathlib
import Definitions.Def_SensLabelCover_DH_LabelCover

namespace SensLabelCover.DH

/-- Theorem 11.1 (Formal version of Theorem 1.2), p. 57 (PDF p. 60). Left vertices `Fin n`, right
vertices `Fin m`, edges `Fin e`, alphabets `Σ_U = Fin a`, `Σ_V = Fin b` (nonempty). The constants
`B, δ, c, K, n_min` are absolute (chosen before `n` and `g`); `Ω(n^δ)` is `≥ c n^δ`, every `O(1)`
exponent and factor is `K`; `log` is natural. Every map `A` from instances to distributions on
assignments with expected value `≥ 1/g` on each satisfiable member has some member and some
projection or predicate swap of it with EMD at least `c n^δ`. -/
theorem theorem_11_1 :
    ∃ B δ c K : ℝ, 0 < B ∧ 0 < δ ∧ 0 < c ∧ 0 < K ∧ ∃ nmin : ℕ,
      ∀ n : ℕ, nmin ≤ n → ∀ g : ℝ, 1 < g → g ≤ Real.log (n : ℝ) ^ B →
        ∃ (m e a b : ℕ) (G : BGraph (Fin n) (Fin m) (Fin e))
          (𝓘 : Set (LCInst (Fin n) (Fin e) (Fin a) (Fin b))),
          0 < a ∧ 0 < b ∧ SwapClosed lcAdj 𝓘 ∧
          (∀ A : LCInst (Fin n) (Fin e) (Fin a) (Fin b) →
              PMF (Assignment (Fin n) (Fin m) (Fin a) (Fin b)),
            (∀ I ∈ 𝓘, lcSat G I → 1 / g ≤ expect (A I) (lcVal G I)) →
            ∃ I ∈ 𝓘, ∃ J, lcAdj I J ∧ c * (n : ℝ) ^ δ ≤ emd lcDist (A I) (A J)) ∧
          (m : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) ^ K ∧
          (∀ u, (G.ldeg u : ℝ) ≤ K * g ^ K) ∧ (∀ v, (G.rdeg v : ℝ) ≤ K * g ^ K) ∧
          (b : ℝ) ≤ K * g ^ K ∧ (a : ℝ) ≤ Real.exp (K * g ^ K) := by sorry

end SensLabelCover.DH
