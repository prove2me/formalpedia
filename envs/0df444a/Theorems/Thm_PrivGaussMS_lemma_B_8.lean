-- Prove2me | Theorems.Thm_PrivGaussMS_lemma_B_8
-- name    : PrivGaussMS.lemma_B_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:12:57.270192+00:00
-- url     : https://prove2.me/theorems/37bdf72a-d27e-4b5f-9850-78c78f6b1c66
-- title:
--   Lemma B.8 — determinant bounds: $f_B^{(r)}\le D_A^rf_T^{(r)}$, $D_A\ge e^{a\lambda/n}$, $Z_a\le e^{2(d+1)a}$, density $r_A$ of (27), general position (cost in Theorem B.1)
-- statement:
--   Assume $d,m\ge1$, $0<\alpha<1$, $\eta=\alpha/(2m)$, $q=\lfloor n/3\rfloor$ and (29):
--   $$n\ge256(m+d+1),\qquad n\ge16k\lambda,\qquad \lambda\ge16(d+2+\log n),\qquad a_0\lambda\ge16m\log(1/\eta).$$
--   Then:
--
--   1. If $|A|=a\le k$, $0\prec T_{A^c}\preceq B\preceq T$ and $b\in[n-a,n]$, then $f_B^{(r)}\le D_A^rf_T^{(r)}$ pointwise for $0\le r\le m$.
--   2. If $A$ consists of the first $a\le k$ rows deleted by pruning at a threshold $u\ge\lambda$, and $T$ and $T_{A^c}$ are positive definite, then $D_A\ge e^{a\lambda/n}$.
--   3. For a uniform centered frame and a fixed set $A$ of $a\le k$ rows, $D_A^q$ is integrable,
--   $$Z_a\le e^{2(d+1)a},\qquad Z_a=\Bigl(\frac{n}{n-a}\Bigr)^q\prod_{i=1}^d\prod_{j=1}^q\frac{n-i-2j}{n-a-i-2j},$$
--   and the recipe (27) samples exactly the law with density $r_A=D_A^q/Z_a$ relative to the uniform centered frame.
--   4. A matrix drawn from the uniform centered frame, or from the law with density $r_A$, is almost surely in affine general position: every $d+1$ rows are affinely independent.
--
--   Here $D_\emptyset=Z_0=1$. These bounds make the decision probability of Procedure 5 a valid probability.
--
--   **Formalization Note** The operation counts of part 3 ("evaluated in $O(qd)$ operations", "sampled in $O(n^3)$ operations") are carried by the cost clause of Theorem B.1.
--
--   Differences from the source:
--   - reading: 'a frame with density D_A^q/Z_a can be sampled in O(n³) operations' → the law of the recipe (27) equals the uniform centered frame with density r_A; the two operation counts of part 3 are in the cost clause of Theorem B.1; reason: this item states the algorithms as random maps, which carry no cost (planning decision 10)
--   - generalization: Z_a ≤ e^{2(d+1)a} → also the closed form (44) of Z_a and integrability of D_A^q; reason: (44) is derived on p.62 in the proof of part 3; dropping the extra conjuncts gives the printed statement
--   - encoding: 'the first a ≤ k rows deleted at a threshold at least λ' → the first a entries of the deletion record of pruning at some u ≥ λ, with a ≤ the record's length; reason: the deletion order is the one of the pruning rule (p.37)
--   - encoding: 'Use D_∅ = Z_0 = 1' → built into the definitions DA and Zconst; reason: the paper's convention
--   - encoding: η = α/(2m) → the parameter α ∈ (0, 1) and η := α/(2m) inside the statement; reason: same values; no instance changed
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma B.8, p.50, under (29); formula (44), p.62

import Mathlib
import Definitions.Def_PrivGaussMS_Correction

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace PrivGaussMS

/-- **Lemma B.8** (Determinant bounds for the correction), Moayedi, Yassaee, Ebrahimi, *Optimal
Private Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…), p.50, under
(29): `n ≥ 256(m + d + 1)`, `n ≥ 16kλ`, `λ ≥ 16(d + 2 + log n)`, `a0λ ≥ 16m log(1/η)`.
1. If `|A| = a ≤ k`, `0 ≺ T_{Aᶜ} ⪯ B ⪯ T` and `b ∈ [n − a, n]`, then `f_B^{(r)} ≤ D_A^r f_T^{(r)}` for
   `0 ≤ r ≤ m`.
2. If `A` consists of the first `a ≤ k` rows deleted at a threshold at least `λ`, and the statistics
   before and after deletion are positive definite, then `D_A ≥ e^{aλ/n}`.
3. For a uniform centered frame and a fixed set `A` of `a ≤ k` rows, `Z_a ≤ e^{2(d+1)a}`; a frame
   with density `D_A^q/Z_a` is sampled by (27).
Use `D_∅ = Z_0 = 1`. A matrix drawn from either the uniform distribution or the distribution with
density `r_A` is in affine general position almost surely: every `d + 1` rows are affinely
independent.

**Formalization Note.** Part 1 is pointwise in `Y ∈ ℝ^{r×d}`, for any dataset and any matrix `B`
in the sandwich. Part 2's rows are the first `a` entries of the deletion record of a pruning run at
some threshold `u ≥ λ`, "before deletion" being the full statistic `T`. Part 3 states that `D_A^q`
is integrable (so `Z_a` is a genuine expectation), the bound, the closed form (44) of `Z_a`
(p.62), and that the law of the recipe (27) has density `r_A` with respect to the uniform centered
frame; the operation counts of part 3 ("`O(qd)`", "`O(n³)`") are carried by the cost clause of
Theorem B.1. `η = α/(2m)`. -/
theorem lemma_B_8 (n m d k lam a0 : ℕ) (α : ℝ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hα0 : 0 < α)
    (hα1 : α < 1) (h1 : 256 * (m + d + 1) ≤ n) (h2 : 16 * k * lam ≤ n)
    (h3 : 16 * ((d : ℝ) + 2 + Real.log n) ≤ lam)
    (h4 : 16 * (m : ℝ) * Real.log (1 / (α / (2 * m))) ≤ (a0 : ℝ) * lam) :
    (∀ (x : Fin n → Vec d) (A : Finset (Fin n)) (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      A.card ≤ k → (statI x Aᶜ).PosDef → statI x Aᶜ ≤ B → B ≤ Tstat x →
      (n : ℝ) - A.card ≤ bw B → bw B ≤ n →
      ∀ r : ℕ, r ≤ m → ∀ Y : Matrix (Fin r) (Fin d) ℝ,
        candDensity n r B Y ≤ DA x A ^ r * candDensity n r (Tstat x) Y) ∧
    (∀ (x : Fin n → Vec d) (u : ℝ), (lam : ℝ) ≤ u → ∀ a : ℕ, a ≤ k →
      a ≤ (prune x u).deleted.length →
      (Tstat x).PosDef → (statI x (((prune x u).deleted.take a).toFinset)ᶜ).PosDef →
      Real.exp ((a : ℝ) * lam / n) ≤ DA x ((prune x u).deleted.take a).toFinset) ∧
    (∀ A : Finset (Fin n), A.card ≤ k →
      Integrable (fun U => DA (rowsOf U) A ^ qExp n) (uniformCenteredFrame n d) ∧
      Zconst n d A ≤ Real.exp (2 * ((d : ℝ) + 1) * A.card) ∧
      Zconst n d A = ((n : ℝ) / (n - A.card)) ^ qExp n *
        ∏ i ∈ Finset.Icc 1 d, ∏ j ∈ Finset.Icc 1 (qExp n),
          ((n : ℝ) - i - 2 * j) / ((n : ℝ) - A.card - i - 2 * j) ∧
      law27 n d A = (uniformCenteredFrame n d).withDensity
        (fun U => ENNReal.ofReal (rA n d A U))) ∧
    (∀ A : Finset (Fin n), A.card ≤ k →
      (∀ᵐ U ∂(uniformCenteredFrame n d), ∀ s : Fin (d + 1) ↪ Fin n,
        AffineIndependent ℝ fun i => rowsOf U (s i)) ∧
      (∀ᵐ U ∂(law27 n d A), ∀ s : Fin (d + 1) ↪ Fin n,
        AffineIndependent ℝ fun i => rowsOf U (s i))) := by sorry

end PrivGaussMS
