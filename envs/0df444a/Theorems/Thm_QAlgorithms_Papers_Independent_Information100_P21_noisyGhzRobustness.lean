-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_noisyGhzRobustness
-- name    : QAlgorithms.Papers.Independent.Information100.P21.noisyGhzRobustness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:02:38.689402+00:00
-- url     : https://prove2.me/theorems/2f2c6d21-6185-4e5f-a955-a46f0464a3f3
-- title:
--   X.26 — Theorem X.26 (Full-rank white-noise GHZ family). For 0 ≤ p ≤ 1, let
-- statement:
--   For $n\ge2$, put $D=2^n$ and $\rho_{n,p}=(1-p)G_n^++pI_D/D$, where $0\le p\le1$. Then
--   $$R_g^{\mathrm{FS}_n}(\rho_{n,p})=\max\{0,1-p-2p/D\},\quad R_s^{\mathrm{FS}_n}(\rho_{n,p})=\max\{0,D(1-p)/4-p/2\}=2^{n-2}R_g^{\mathrm{FS}_n}(\rho_{n,p}).$$
--   The state is fully separable exactly when $p\ge D/(D+2)$. For $p>0$, it is full rank and at least $(p/D)I_D$ in PSD order. For $n\ge3$ and $0<p<D/(D+2)$ its gap is strict. The parameter is the white-noise weight.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 30, X.26 — Theorem X.26 (Full-rank white-noise GHZ family). For 0 ≤ p ≤ 1, let

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 30, Theorem X.26 (Full-rank white-noise GHZ family). For 0 ≤ p ≤ 1, let. -/
theorem noisyGhzRobustness (n : ℕ) (hn : 2≤n) (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
  QAlgorithms.IsDensityMatrix (noisyGHZ n p) ∧
  fsR (fun _ : Fin n => 2) false (noisyGHZ n p)=max 0 (1-p-2*p/(2^n:ℝ)) ∧
  fsR (fun _ : Fin n => 2) true (noisyGHZ n p)=max 0 ((2^n:ℝ)*(1-p)/4-p/2) ∧
  fsR (fun _ : Fin n => 2) true (noisyGHZ n p)=
    (2:ℝ)^(n-2)*fsR (fun _ : Fin n => 2) false (noisyGHZ n p) ∧
  (noisyGHZ n p∈fs (fun _ : Fin n => 2) ↔ (2^n:ℝ)/((2^n:ℝ)+2)≤p) ∧
  (0<p → (noisyGHZ n p).PosDef ∧ (noisyGHZ n p-(p/(2^n:ℝ):ℂ) • 1).PosSemidef) ∧
  (3≤n → 0<p → p<(2^n:ℝ)/((2^n:ℝ)+2) →
    fsR (fun _ : Fin n => 2) false (noisyGHZ n p)<fsR (fun _ : Fin n => 2) true (noisyGHZ n p)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
