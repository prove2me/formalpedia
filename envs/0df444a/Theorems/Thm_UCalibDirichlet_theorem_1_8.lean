-- Prove2me | Theorems.Thm_UCalibDirichlet_theorem_1_8
-- name    : UCalibDirichlet.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:50.962111+00:00
-- url     : https://prove2.me/theorems/430a212a-1541-4c52-9bfe-9c671ae09419
-- title:
--   Theorem 1.8 — Algorithm 1 has regret $O(K\log T\cdot L_F(T))$ for every proper loss; every forecaster has regret $\ge L_F(T)$
-- statement:
--   Let $\Delta_K$ be the probability simplex, $\Lambda_F$ the Dirichlet potential, $V_F$ the smoothing penalty (9), $W^i_F$ the curvature (11), and
--   $$L_F(T)=T\sup_{q\in\Delta_K}\Big\{\mathbb E_{M\sim\mathrm{Mult}(T,q)}\big[F(M/T)\big]-F(q)\Big\}.$$
--   There is a universal constant $C$ such that:
--   1. for all $K\ge1$, $T\ge1$ and every convex $F:\Delta_K\to\mathbb R$ normalized by (4),
--   $$V_F(T)+\Lambda_F(\mathbf 1)\le C\,K\log(eT)\,L_F(T);$$
--   2. for every convex $F:\Delta_K\to\mathbb R$, $i\in[K]$ and $a\in\mathbb N^K$ with $a_i\ge1$ and $\|a_{-i}\|_1\ge1$,
--   $$W^i_F(a)\le C\,L_F(\|a\|_1);$$
--   3. for all $K\ge1$ and $T\ge K$, for every proper loss $\ell_F$ with finite potential $F$ and every outcome sequence $i_1,\dots,i_T$, the expected regret of Algorithm 1 satisfies
--   $$\mathrm{Reg}_F(T)\le C\,K\log(eT)\,L_F(T);$$
--   4. for all $K\ge1$, $T\ge1$, every proper loss $\ell_F$ with finite potential $F$ and every forecaster (whose expected losses $\mathbb E[\ell_F(P_t,i)]$ are defined), there is an outcome sequence $i_1,\dots,i_T$ with
--   $$\mathrm{Reg}_F(T)\ge L_F(T).$$
--
--   Up to the factor $K\log T$, the single loss-independent Algorithm 1 is minimax optimal for every proper loss simultaneously, and $L_F(T)$ characterizes the minimax regret of each proper loss.
--
--   Differences from the source:
--   - reading: O(K log(T) L_F(T)), O(L_F(‖a‖₁)) → ≤ C·K·log(eT)·L_F(T) and ≤ C·L_F(‖a‖₁) with one C quantified before everything; reason: the literal log T = 0 at T = 1 would force V_F(1) + Λ_F(𝟏) ≤ 0, false for F(p) = ½‖p − u‖², K = 2 (Λ_F(𝟏) > 0); log(eT) is the paper's own form (Lemma 2.3, proof of Theorem 1.8, p.14) and is at most 3·log T for T ≥ 2; O(·) constants are universal (independent of K, T, F, ℓ, i, a)
--   - generalization: F normalized by (4) (standing convention, p.3) in the W, regret and lower-bound clauses → no normalization assumed in clauses 2–4; reason: W^i_F, L_F and the regret are unchanged when an affine function is added to F (Bernstein operators reproduce affine functions; the covariance with a constant vanishes; ℓ_F changes by p-independent terms), so the normalized case implies the general one
--   - generalization: a ∈ ℕ^K_+ (positive integer counts) → a ∈ ℕ^K with a_i ≥ 1 and ∑_{j≠i} a_j ≥ 1; reason: positive counts satisfy these (with K ≥ 2); a vector with zero coordinates off i reduces to the same statement on a face of the simplex, where L_F is at most its value on Δ_K
--   - encoding: K, T unrestricted in the display → K ≥ 1 in clauses 1, 3, 4; T ≥ 1 in clauses 1 and 4; reason: Δ_0 is empty and L_F(0) involves M/0; the horizon is a positive integer
--   - encoding: proper loss ℓ_F; expected loss; randomized forecaster; adversary → EReal-valued ℓ with IsProperLoss and HasFiniteBayesRisk, F = bayesPot ℓ; expLoss; forecaster = map from past outcomes to a law on Δ_K (IsForecaster); fixed outcome sequence; reason: the paper fixes the outcome sequence (p.3, p.14); expected regret against a fixed sequence depends on a randomized forecaster only through these laws; the paper allows the value +∞
--   - encoding: Cov in W^i_F (11) → W valued in [0, +∞] via the symmetric form (12); reason: the paper's equivalent form; clause 2 asserts finiteness
--   - encoding: expectation E[ℓ(P_t, i_t)] for an arbitrary forecaster → clause 4 assumes p ↦ ℓ(p, j) a.e.-measurable under each forecast law σ t h of the first T rounds; reason: the expectation in (2) presupposes it; it only excludes forecasters whose regret is undefined, and puts no condition on ℓ itself
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem 1.8, display (14), p.6

import Mathlib
import Definitions.Def_UCalibDirichlet_IsProperLoss
import Definitions.Def_UCalibDirichlet_HasFiniteBayesRisk
import Definitions.Def_UCalibDirichlet_bayesPot
import Definitions.Def_UCalibDirichlet_Lam
import Definitions.Def_UCalibDirichlet_VF
import Definitions.Def_UCalibDirichlet_W
import Definitions.Def_UCalibDirichlet_LF
import Definitions.Def_UCalibDirichlet_IsNormalized
import Definitions.Def_UCalibDirichlet_IsForecaster
import Definitions.Def_UCalibDirichlet_regret
import Definitions.Def_UCalibDirichlet_alg1

namespace UCalibDirichlet

/-- **Theorem 1.8 (formal main result).** Frongillo, Luo, Mehta & Schneider, *Near-Optimal Regret in
U-Calibration for Every Proper Loss* (manuscript, STOC 2027 submission), Theorem 1.8, display (14),
p.6: "For any convex function `F`, `i ∈ [K]`, and `a ∈ ℕ^K_+`, we have
`V_F(T) + Λ_F(𝟏) = O(K log(T) L_F(T))` and `W^i_F(a) = O(L_F(‖a‖₁))`, where (with Mult being the
multinomial distribution) `L_F(T) = T sup_{q∈Δ_K} { E_{M∼Mult(T,q)}[F(M/T)] − F(q) }`. (14)
Consequently, for `T ≥ K`, Algorithm 1 ensures `Reg_F(T) = O(K log(T) L_F(T))` for every proper
loss `ℓ_F` simultaneously. Moreover, fixing a proper loss `ℓ_F`, for any forecaster, there exists
a sequence of outcomes `i_1, …, i_T` such that `Reg_F(T) ≥ L_F(T)`."

One universal constant `C` serves all three `O(·)`, and:
1. for `K ≥ 1`, `T ≥ 1` and every convex `F` on `Δ_K` normalized by (4):
   `V_F(T) + Λ_F(𝟏) ≤ C K log(eT) L_F(T)`;
2. for every convex `F` on `Δ_K`, `i`, and `a ∈ ℕ^K` with `a_i ≥ 1` and `‖a_{−i}‖₁ ≥ 1`:
   `W^i_F(a) ≤ C L_F(‖a‖₁)` (in particular `W^i_F(a)` is finite);
3. for `K ≥ 1`, `T ≥ K`, every proper loss `ℓ` with finite Bayes risk and every outcome sequence:
   the expected regret of Algorithm 1 is at most `C K log(eT) L_F(T)`, `F = bayesPot ℓ`;
4. for `K ≥ 1`, `T ≥ 1`, every proper loss `ℓ` with finite Bayes risk and every forecaster `σ`
   whose expected losses are defined (`ℓ(·, j)` a.e.-measurable under each forecast law of the first
   `T` rounds), some outcome sequence gives `Reg(T) ≥ L_F(T)`.

**Formalization Note.** `O(K log(T) ·)` is read as `≤ C K log(eT) ·` with `C` universal (quantified
before everything else): at `T = 1` the literal `log T = 0` would force `V_F(1) + Λ_F(𝟏) ≤ 0`, false
for `F(p) = ½‖p − u‖²`, and `log(eT)` is the paper's own form (Lemma 2.3, proof of Theorem 1.8).
Normalization (4) is assumed only in clause 1: `W`, `L_F` and the regret are invariant under adding
an affine function to `F`, so clauses 2–4 hold for normalized `F` iff for all `F`. In clause 2,
`ℕ^K_+` is generalized to `a_j ≥ 0` for `j ≠ i` with `a_i ≥ 1`, `‖a_{−i}‖₁ ≥ 1` (all that
`Beta(a_i, ‖a_{−i}‖₁)` needs). Forecasters are maps from past outcomes to laws on `Δ_K`
(`Forecaster`, `IsForecaster`); losses are `EReal`-valued and expected losses are `expLoss`. The
outcome sequence is fixed in advance (p.3, p.14). In clause 4 the loss is assumed a.e.-measurable
under each forecast law `σ t h` (`t < T`), which is exactly what the expectation `E[ℓ(P_t, i_t)]` in
(2) presupposes for an arbitrary forecaster; no measurability of `ℓ` itself is assumed. -/
theorem theorem_1_8 : ∃ C : ℝ,
    (∀ (K : ℕ), 1 ≤ K → ∀ (T : ℕ), 1 ≤ T → ∀ F : (Fin K → ℝ) → ℝ,
      ConvexOn ℝ (stdSimplex ℝ (Fin K)) F → IsNormalized F →
        VF F T + Lam F (fun _ => 1) ≤ C * K * Real.log (Real.exp 1 * T) * LF F T) ∧
    (∀ (K : ℕ) (F : (Fin K → ℝ) → ℝ), ConvexOn ℝ (stdSimplex ℝ (Fin K)) F →
      ∀ (i : Fin K) (a : Fin K → ℕ), 1 ≤ a i → 1 ≤ ∑ j ∈ Finset.univ.erase i, a j →
        W F i (fun j => (a j : ℝ)) ≤ ENNReal.ofReal (C * LF F (∑ j, a j))) ∧
    (∀ (K : ℕ), 1 ≤ K → ∀ (T : ℕ), K ≤ T → ∀ ℓ : (Fin K → ℝ) → Fin K → EReal,
      IsProperLoss ℓ → HasFiniteBayesRisk ℓ → ∀ i : Fin T → Fin K,
        regret ℓ alg1 i ≤ ((C * K * Real.log (Real.exp 1 * T) * LF (bayesPot ℓ) T : ℝ) : EReal)) ∧
    (∀ (K : ℕ), 1 ≤ K → ∀ (T : ℕ), 1 ≤ T → ∀ ℓ : (Fin K → ℝ) → Fin K → EReal,
      IsProperLoss ℓ → HasFiniteBayesRisk ℓ →
      ∀ σ : Forecaster K, IsForecaster σ →
      (∀ t, t < T → ∀ (h : Fin t → Fin K) (j : Fin K), AEMeasurable (fun p => ℓ p j) (σ t h)) →
      ∃ i : Fin T → Fin K,
        ((LF (bayesPot ℓ) T : ℝ) : EReal) ≤ regret ℓ σ i) := by sorry

end UCalibDirichlet
