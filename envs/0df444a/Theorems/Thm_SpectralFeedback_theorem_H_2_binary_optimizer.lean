-- Prove2me | Theorems.Thm_SpectralFeedback_theorem_H_2_binary_optimizer
-- name    : SpectralFeedback.theorem_H_2_binary_optimizer
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:01.289118+00:00
-- url     : https://prove2.me/theorems/3d93230b-4540-47f7-84f4-0f00eb53dfcf
-- title:
--   Theorem H.2 — one binary decomposition optimizes every concave symmetric monotone reward: $\mathcal G^F_{2,s}(R)=2F(c/2)$
-- statement:
--   Fix an integer $s\ge1$ and a positive semidefinite $R\in\mathbb C^{d\times d}$ (any $d$, any trace). Let $\lambda_1\ge\dots\ge\lambda_{2s}\ge0$ be the first $2s$ eigenvalues of $R$, padded by zeros, and put
--
--   $$
--   c_i=\lambda_i+\lambda_{2s+1-i},\qquad1\le i\le s .
--   $$
--
--   1. For every admissible $F$ (continuous, symmetric, concave, coordinatewise nondecreasing on $\mathbb R^s_+$, with $F(0)=0$) the maximum $\mathcal G^F_{2,s}(R)$ of $f_{F,s}(A_1)+f_{F,s}(A_2)$ over $A_1,A_2\succeq0$ with $A_1+A_2=R$ exists and
--   $$
--   \mathcal G^F_{2,s}(R)=2F(c/2).
--   $$
--   2. In every decreasing spectral basis $e_1,\dots,e_d$ of $R$, the atoms
--   $$
--   T_\pm=\sum_{i=1}^s v_{i,\pm}v_{i,\pm}^*,\qquad v_{i,\pm}=\frac{\sqrt{\lambda_i}\,e_i\pm\sqrt{\lambda_{2s+1-i}}\,e_{2s+1-i}}{\sqrt2}
--   $$
--   (coordinates beyond dimension $d$ omitted) are positive semidefinite of rank at most $s$ and sum to the active matrix $R_{[\min(d,2s)]}$; the tail $\sum_{j>2s}\lambda_je_je_j^*$ is positive semidefinite and $(T_++\text{tail})+T_-=R$.
--   3. These atoms do not depend on $F$: for **every** admissible $F$,
--   $$
--   f_{F,s}(T_+)+f_{F,s}(T_-)=2F(c/2)\quad\text{and}\quad f_{F,s}(T_++\text{tail})+f_{F,s}(T_-)=2F(c/2).
--   $$
--   4. If $F$ is moreover homogeneous of degree one, then $\mathcal G^F_{2,s}(R)=F(c)$.
--
--   For the measurement payoff $F=\chi_s$ this is the exact binary-feedback discrimination value of the paper; in general it gives one explicit, payoff-independent optimal binary decomposition for a whole class of concave spectral rewards.
--
--   **Formalization Note** "$\mathcal G=v$" is `IsGreatest (rewardSet s F 2 R) v`; $c$ is `pairedVec R s`; $T_\pm$ is `pairAtom R U s (±1)` for every unitary $U$ with $R=U\,\mathrm{diag}(\lambda)\,U^*$; `Admissible s F` places all hypotheses on the orthant. The atoms are fixed before $F$ is quantified.
--
--   Differences from the source:
--   - encoding: matrices on $\mathbb C^d$, eigenvalues $\lambda_i$ ($1$-based, padded by zeros) → `Matrix (Fin d) (Fin d) ℂ` for every `d : ℕ`; `eigDesc A (i-1)` (0-based, padded by zeros); reason: Lean indexing convention; same instances
--   - encoding: $\mathcal G^F_{2,s}(R)=v$ (a maximum) → `IsGreatest (rewardSet s F 2 R) v`; reason: the maximum exists and equals $v$; same content
--   - encoding: $F:\mathbb R^s_+\to\mathbb R_+$ continuous, symmetric, concave, coordinatewise nondecreasing, $F(0)=0$ → `Admissible s F`: $F$ on `Fin s → ℝ` with `ContinuousOn`, symmetry, `ConcaveOn`, `MonotoneOn` on `orthant s`, and `F 0 = 0`; no separate nonnegativity clause; reason: values off the orthant are never used; $F\ge0$ on the orthant follows from monotonicity and $F(0)=0$
--   - encoding: $e_i$ in a spectral basis; $T_\pm$ with coordinates beyond $d$ omitted → every unitary `U` with `R = U * diagonal (eigDesc R) * star U`; `pairAtom R U s (±1) = U (∑ v vᴴ) Uᴴ` on `Fin d`; reason: under repeated eigenvalues the basis is not unique, and the statement holds for each; indices ≥ d do not exist in `Fin d`
--   - reading: For every admissible $F$, the same active atoms attain this value … Add the tail beyond $2s$ to $T_+$ for the full problem → for every `U`: `T±` PSD, rank ≤ s, `T₊ + T₋ = activePart R U (min d (2s))`, tail PSD, `(T₊ + tail) + T₋ = R`, and for every admissible `F` both `(T₊, T₋)` and `(T₊ + tail, T₋)` have total reward `2F(c/2)`; reason: "active atoms" are rank-≤ s atoms of the active matrix (Lemma H.1); "attain" is read for both the active pair and the full-input pair, with the atoms fixed before F
--   - encoding: $F$ homogeneous of degree one → `∀ t ≥ 0, ∀ x ∈ orthant s, F (t • x) = t * F x`; reason: degree-one homogeneity on $\mathbb R^s_+$; same content
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem H.2, (H.1), p.109 (PDF p.111); main-text Theorem 4.2, (4.1), p.6 (PDF p.8)

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_pairAtom

open scoped ComplexOrder

namespace SpectralFeedback

/-- **Theorem H.2** (One binary decomposition optimizes every such reward; Qi, *Spectral Structure
and Exact Arithmetic of Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.109
(PDF p.111); main-text twin Theorem 4.2, (4.1), p.6). Fix `s ≥ 1` and `R ⪰ 0` on `ℂ^d`. Let
`λ₁ ≥ ⋯ ≥ λ_{2s} ≥ 0` be the first `2s` eigenvalues of `R`, padded by zeros, and
`c_i = λ_i + λ_{2s+1−i}`, `1 ≤ i ≤ s`. Then, for every admissible `F` (§H.1.1, p.108),
`G^F_{2,s}(R) = 2F(c/2)` (H.1). For every admissible `F` the same active atoms
`T_± = ∑_{i=1}^s v_{i,±} v_{i,±}*`, `v_{i,±} = (√λ_i e_i ± √λ_{2s+1−i} e_{2s+1−i})/√2`, attain
this value; coordinates beyond dimension `d` are omitted, and the tail beyond `2s` is added to `T₊`
for the full problem. If `F` is homogeneous of degree one, the value simplifies to `F(c)`.

The four conjuncts: (1) the maximum exists and equals `2F(c/2)`; (2) for every decreasing spectral
basis `U`, `T_±` (built from `R` and `U` only, before `F`) are positive semidefinite of rank at most
`s`, sum to the active matrix `R_{[min(d,2s)]}`, and with the (positive semidefinite) tail added to
`T₊` sum to `R`; (3) for every admissible `F`, both the active pair `(T₊, T₋)` and the full-input
pair `(T₊ + tail, T₋)` have total reward `2F(c/2)`; (4) degree-one homogeneity gives the value
`F(c)`.

**Formalization Note** Matrices are `Matrix (Fin d) (Fin d) ℂ` for any `d` (including `d < 2s` and
`d > 2s`); eigenvalues are `eigDesc` (0-based, padded by zeros); `c` is `pairedVec R s`; the maximum
is `IsGreatest`; "in a spectral basis" is every unitary `U` with `R = U diag(λ) U*`; `F`'s hypotheses
hold on `ℝ^s_+` only (`Admissible`). -/
theorem theorem_H_2_binary_optimizer (s : ℕ) (hs : 1 ≤ s) {d : ℕ}
    (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosSemidef) :
    (∀ F : (Fin s → ℝ) → ℝ, Admissible s F →
      IsGreatest (rewardSet s F 2 R) (2 * F (fun i => pairedVec R s i / 2))) ∧
    (∀ U : Matrix (Fin d) (Fin d) ℂ, IsSortedEigenbasis R U →
      (pairAtom R U s 1).PosSemidef ∧ (pairAtom R U s (-1)).PosSemidef ∧
      (pairAtom R U s 1).rank ≤ s ∧ (pairAtom R U s (-1)).rank ≤ s ∧
      pairAtom R U s 1 + pairAtom R U s (-1) = activePart R U (min d (2 * s)) ∧
      (tailPart R U s).PosSemidef ∧
      (pairAtom R U s 1 + tailPart R U s) + pairAtom R U s (-1) = R ∧
      ∀ F : (Fin s → ℝ) → ℝ, Admissible s F →
        reward s F (pairAtom R U s 1) + reward s F (pairAtom R U s (-1)) =
            2 * F (fun i => pairedVec R s i / 2) ∧
        reward s F (pairAtom R U s 1 + tailPart R U s) + reward s F (pairAtom R U s (-1)) =
            2 * F (fun i => pairedVec R s i / 2)) ∧
    (∀ F : (Fin s → ℝ) → ℝ, Admissible s F →
      (∀ t : ℝ, 0 ≤ t → ∀ x ∈ orthant s, F (t • x) = t * F x) →
      IsGreatest (rewardSet s F 2 R) (F (pairedVec R s))) := by sorry

end SpectralFeedback
