-- Prove2me | Theorems.Thm_SensLabelCover_DH_lemma_5_2
-- name    : SensLabelCover.DH.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:38:16.826555+00:00
-- url     : https://prove2.me/theorems/c3a9a282-93f1-4b65-b5d2-c520bbf35fbb
-- title:
--   Lemma 5.2 — alphabet reduction: satisfiability, $\mathbb E\,\mathrm{val}_I(R_I(\pi'))\ge(\mathbb E\,\mathrm{val}_{I'}(\pi'))^2-\eta^3$, transfer parameters $(k,\,1+\Delta_U/\delta_V,\,1/\delta_V)$
-- statement:
--   Let $\mathcal I$ be a swap-closed family of left-predicate Label Cover instances on a common graph $G=(U,V,E)$ and alphabets $\Sigma_U,\Sigma_V$, with maximum left degree $\Delta_U$ and minimum right degree $\delta_V\ge1$. Fix $\eta\in(0,1/4)$ and a code $C:\Sigma_V\to\hat\Sigma_V^k$ ($k\ge1$) of relative distance $1-\eta^3$, and let $I'=T_{AR}(I)$. Then:
--   1. if $I\in\mathcal I$ is satisfiable, $T_{AR}(I)$ is satisfiable;
--   2. for every $I\in\mathcal I$ and every random labeling $\pi'$ of $I'$,
--   $$\mathbb E\big[\mathrm{val}_I(R_I(\pi'))\big]\ge\big(\mathbb E[\mathrm{val}_{I'}(\pi')]\big)^2-\eta^3;$$
--   3. $T_{AR}$ with the recoveries $\mathcal R_I(\mu)=(R_I)_\#\mu$ has sensitivity-transfer parameters
--   $$C_{\mathcal T}=k,\qquad C_{\mathcal R}=1+\frac{\Delta_U}{\delta_V},\qquad D_{\mathcal R}=\frac1{\delta_V}.$$
--
--   Alphabet reduction replaces the right alphabet by the code alphabet while losing only a square and $\eta^3$ in value and a bounded factor in sensitivity.
--
--   Differences from the source:
--   - generalization: the code chosen from Proposition 5.1, whose alphabet and length satisfy $|\hat\Sigma_V|=O(\eta^{-6})$ and $k=O(\eta^{-6}\log|\Sigma_V|)$ → any code $C:\Sigma_V\to\hat\Sigma_V^k$ with $k\ge1$ and relative distance $1-\eta^3$, with no size condition; reason: items 1–3 use only the distance and $k\ge1$, and the paper's code is one such code. The two size bounds describe that code (Proposition 5.1, not posed), not the reduction.
--   - reading: sensitivity-transfer parameters → nonnegative reals; reason: they bound nonnegative quantities (Definition 3.1).
--   - encoding: maximum left degree and minimum right degree $\delta_V\ge1$ → `G.maxLDeg`, `G.minRDeg` with no isolated right vertex; the average degrees $\bar d_U,\bar d_V$, named but unused in the statement, are omitted; reason: same instances.
--   - encoding: $R_I$ sampling each $\pi(v)$ from $p_v$ independently → one uniform incident edge per right vertex, returning its projected left label; reason: same law (the paper's own implementation, p. 27).
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 26 (PDF 29), Lemma 5.2

import Mathlib
import Definitions.Def_SensLabelCover_DH_AlphabetReduction

namespace SensLabelCover.DH

/-- Lemma 5.2 (Sensitivity transfer through alphabet reduction), p. 26 (PDF p. 29), for every code
`C : Σ_V → Σ̂_V^k` of relative distance `1 − η³` (the paper's code from Proposition 5.1 is one).
`Δ_U = G.maxLDeg`, `δ_V = G.minRDeg ≥ 1`; `ℛ_I(μ) := (R_I)_#μ`. -/
theorem lemma_5_2 {U V E SU SV : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype SU] [DecidableEq SU] [Fintype SV] [DecidableEq SV]
    (G : BGraph U V E) (hD : ∀ v, 0 < G.rdeg v) (𝓘 : Set (LCInst U E SU SV))
    (h𝓘 : SwapClosed lcAdj 𝓘) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 4) {k : ℕ} {SH : Type}
    [Fintype SH] [DecidableEq SH] (C : SV → Fin k → SH) (hC : IsCode C (η ^ 3)) :
    (∀ I ∈ 𝓘, lcSat G I → lcSat (arGraph G k) (tar C I)) ∧
      (∀ I ∈ 𝓘, ∀ μ : PMF (Assignment U (V × Fin k) SU SH),
        (expect μ (lcVal (arGraph G k) (tar C I))) ^ 2 - η ^ 3 ≤
          expect (μ.bind (recoverAR G I hD)) (lcVal G I)) ∧
      IsTransferParams lcAdj lcAdj lcDist lcDist 𝓘 (tar C)
        (fun I (μ : PMF (Assignment U (V × Fin k) SU SH)) => μ.bind (recoverAR G I hD))
        (k : ℝ) (1 + (G.maxLDeg : ℝ) / (G.minRDeg : ℝ)) (1 / (G.minRDeg : ℝ)) := by sorry

end SensLabelCover.DH
