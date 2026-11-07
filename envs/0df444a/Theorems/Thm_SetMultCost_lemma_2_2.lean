-- Prove2me | Theorems.Thm_SetMultCost_lemma_2_2
-- name    : SetMultCost.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:07.073224+00:00
-- url     : https://prove2.me/theorems/fa95d69b-85e3-406d-a915-5d9a486f1e2f
-- title:
--   Lemma 2.2 — properties of the relative rank
-- statement:
--   Assume $n^\alpha\ge d\ge1$ and $\alpha\in(0,1]$, and fix $\pi=(\mathcal P,\mathcal N)$.
--
--   1. (Subadditive) For $P_1,\dots,P_s$ set-multilinear on the same parts,
--   $$\mathrm{relrk}_{n,\alpha,\pi}(P_1+\cdots+P_s)\le\mathrm{relrk}_{n,\alpha,\pi}(P_1)+\cdots+\mathrm{relrk}_{n,\alpha,\pi}(P_s).$$
--   2. (Multiplicative) For a set-multilinear product $P_1\cdots P_s$, with $P_i$ set-multilinear along $\pi_i=(\mathcal P_i,\mathcal N_i)$,
--   $$\mathrm{relrk}_{n,\alpha,\pi}(P_1\cdots P_s)=\mathrm{relrk}_{n,\alpha,\pi_1}(P_1)\cdots\mathrm{relrk}_{n,\alpha,\pi_s}(P_s).$$
--   3. (Approximation)
--   $$\frac{\mathrm{rank}\,M_{n,\alpha,\pi}(P)}{n^{(d_{\mathcal N}+\alpha d_{\mathcal P})/2}}\le\mathrm{relrk}_{n,\alpha,\pi}(P)\le\frac{2\,\mathrm{rank}\,M_{n,\alpha,\pi}(P)}{n^{(d_{\mathcal N}+\alpha d_{\mathcal P})/2}}.$$
--   4. (Upper bound) If $n^\alpha>1$,
--   $$\mathrm{relrk}_{n,\alpha,\pi}(P)\le\frac{1}{n^{|\alpha d_{\mathcal P}-d_{\mathcal N}|/2}}\cdot\frac{1}{(1-1/n^\alpha)^{d_{\mathcal P}/2}}.$$
--
--   These four facts are all the mission uses of the measure.
--
--   Differences from the source:
--   - generalization: polynomials on all d parts (items 1, 3, 4) → polynomials on any subset T of the parts, with d_P = |T ∩ P|, d_N = |T \ P|; reason: T = [d] is the page; item 2 needs subsets anyway
--   - encoding: item 4 with no restriction on n^α → the hypothesis 1 < n^α; reason: the page has 1/0 at n^α = 1, and Lean assigns that the value 0
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Lemma 2.2, p.9

import Mathlib
import Definitions.Def_SetMultCost_IsSetMultilinearOn
import Definitions.Def_SetMultCost_relrk

namespace SetMultCost

/-- **Lemma 2.2 (Properties of the complexity measure).** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.9: "Assume n^α ≥ d ≥ 1. 1.
(Subadditive). Consider P1, . . . , Ps to be set-multilinear polynomials along the partition π.
relrkn,α,π(P1 + · · · + Ps) ≤ relrkn,α,π(P1) + · · · + relrkn,α,π(Ps). 2. (Multiplicative). Consider a
set-multilinear product P = P1 · . . . · Ps where each Pi is set-multilinear along the partition πi =
(Pi, Ni) with P = ⊔ Pi and N = ⊔ Ni. Then, relrkn,α,π(P1 · . . . · Ps) = relrkn,α,π1(P1) · · ·
relrkn,α,πs(Ps). 3. An approximation of the measure is given by rank(Mn,α,π(P))/n^{(dN+αdP)/2} ≤
relrkn,α,π(P) ≤ 2 · rank(Mn,α,π(P))/n^{(dN+αdP)/2}. 4. The measure is upper bounded by relrkn,α,π(P)
≤ 1/n^{|αdP−dN|/2} · 1/(1 − 1/n^α)^{dP/2}."

**Formalization Note.** Stated for polynomials on any set `T` of parts, with `d_P = |T ∩ P|` and
`d_N = |T \ P|`; `T = Finset.univ` is the page's form, and clause 2 is how the partitions `πᵢ`
enter. Clause 4 adds `1 < n^α`: at `n^α = 1` the page's right side has `1/0`, while Lean's value is
`0`. `α ∈ (0, 1]` is the standing range of p.8. -/
theorem lemma_2_2 (F : Type*) [Field F] {d n : ℕ} (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hd : 1 ≤ d)
    (hn : (d : ℝ) ≤ (n : ℝ) ^ α) (P : Finset (Fin d)) :
    (∀ (T : Finset (Fin d)) (s : ℕ) (Q : Fin s → MvPolynomial (Var d (sizeFn P ⌊(n : ℝ) ^ α⌋₊ n)) F),
      (∀ i, IsSetMultilinearOn Sigma.fst T (Q i)) →
      relrk n α P T (∑ i, Q i) ≤ ∑ i, relrk n α P T (Q i)) ∧
    (∀ (s : ℕ) (Q : Fin s → MvPolynomial (Var d (sizeFn P ⌊(n : ℝ) ^ α⌋₊ n)) F)
      (Ts : Fin s → Finset (Fin d)),
      (∀ i, IsSetMultilinearOn Sigma.fst (Ts i) (Q i)) →
      (∀ i j, i ≠ j → Disjoint (Ts i) (Ts j)) →
      relrk n α P (Finset.univ.biUnion Ts) (∏ i, Q i) = ∏ i, relrk n α P (Ts i) (Q i)) ∧
    (∀ (T : Finset (Fin d)) (Q : MvPolynomial (Var d (sizeFn P ⌊(n : ℝ) ^ α⌋₊ n)) F),
      IsSetMultilinearOn Sigma.fst T Q →
      ((coeffMatrix P T Q).rank : ℝ) /
          (n : ℝ) ^ (((T \ P).card + α * (T ∩ P).card) / 2) ≤ relrk n α P T Q ∧
      relrk n α P T Q ≤ 2 * ((coeffMatrix P T Q).rank : ℝ) /
          (n : ℝ) ^ (((T \ P).card + α * (T ∩ P).card) / 2)) ∧
    (1 < (n : ℝ) ^ α →
      ∀ (T : Finset (Fin d)) (Q : MvPolynomial (Var d (sizeFn P ⌊(n : ℝ) ^ α⌋₊ n)) F),
      IsSetMultilinearOn Sigma.fst T Q →
      relrk n α P T Q ≤ 1 / (n : ℝ) ^ (|α * ((T ∩ P).card : ℝ) - ((T \ P).card : ℝ)| / 2) *
        (1 / (1 - 1 / (n : ℝ) ^ α) ^ (((T ∩ P).card : ℝ) / 2))) := by sorry

end SetMultCost
