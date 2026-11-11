-- Prove2me | Theorems.Thm_SensLabelCover_DH_lemma_5_3
-- name    : SensLabelCover.DH.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:38:25.212136+00:00
-- url     : https://prove2.me/theorems/b12102cb-bee4-4620-84c5-3ce48a2750b6
-- title:
--   Lemma 5.3 — $\mathrm{red}_\varepsilon$: degree $\Theta(1/\varepsilon)$, value $4\sqrt\varepsilon\to\varepsilon$, SwapDist factor $C_{red}\varepsilon^{-7}\log(2|\Sigma_V|)$ (corrected: log(2|Σ_V|))
-- statement:
--   There is $c_0>0$ such that for every $c_{AR}\ge c_0$ and every $K>0$ there are constants $C_{red},C_V,C_U,c,C>0$ with the following property. Let $0<\varepsilon<1/16$, let $\mathcal I$ be a swap-closed family of left-predicate Label Cover instances on a common graph $G=(U,V,E)$ and common alphabets $\Sigma_U,\Sigma_V$, with no isolated right vertices, $|U|=n$, $|V|=m$, average degrees $\bar d_U=|E|/n$, $\bar d_V=|E|/m$, maximum left degree $\Delta_U$ and minimum right degree $\delta_V$. Let $C:\Sigma_V\to\hat\Sigma_V^k$ be a code ($k\ge1$) of relative distance $1-(\varepsilon/4)^3$ with $k\le K\varepsilon^{-6}\log(2|\Sigma_V|)$. Fix, for the alphabet-reduced graph, $[D,d_\varepsilon,\lambda]$-expanders with $\lambda\le\sqrt\varepsilon$ and incidence orderings, where $d_\varepsilon=2\lfloor c_{AR}/(2\varepsilon)\rfloor$, and let $\mathrm{red}_\varepsilon$ and $R_{\varepsilon,I}$ use these choices. Then $\mathrm{red}_\varepsilon(I)$ has left vertex set $U$,
--   $$|V'|\le C_V\,\varepsilon^{-6}m\,\bar d_V\log(2|\Sigma_V|),\qquad \bar d_{U'}\le C_U\,\bar d_U\,\varepsilon^{-7}\log(2|\Sigma_V|),$$
--   every right vertex has degree $d_\varepsilon$ with $c/\varepsilon\le d_\varepsilon\le C/\varepsilon$, and:
--   1. if $I\in\mathcal I$ is satisfiable, so is $\mathrm{red}_\varepsilon(I)$;
--   2. if a random assignment $\pi'$ of $\mathrm{red}_\varepsilon(I)$ has $\mathbb E[\mathrm{val}_{\mathrm{red}_\varepsilon(I)}(\pi')]\ge4\sqrt\varepsilon$, then $\mathbb E[\mathrm{val}_I(R_{\varepsilon,I}(\pi'))]\ge\varepsilon$;
--   3. for all $I,\tilde I\in\mathcal I$, $\ \mathrm{SwapDist}(\mathrm{red}_\varepsilon(I),\mathrm{red}_\varepsilon(\tilde I))\le C_{red}\,\varepsilon^{-7}\log(2|\Sigma_V|)\cdot\mathrm{SwapDist}(I,\tilde I)$;
--   4. for every $I\in\mathcal I$ and assignments $\pi',\tilde\pi'$ of $\mathrm{red}_\varepsilon(I)$, $\ \mathrm{EMD}(R_{\varepsilon,I}(\pi'),R_{\varepsilon,I}(\tilde\pi'))\le(1+\Delta_U/\delta_V)\,d_H(\pi',\tilde\pi')$;
--   5. if $I,\tilde I\in\mathcal I$ differ by one swap, then for every assignment $\pi'$ of their common reduced graph, $\ \mathrm{EMD}(R_{\varepsilon,I}(\pi'),R_{\varepsilon,\tilde I}(\pi'))\le1/\delta_V$.
--
--   The combined reduction is the step the paper repeats at every round of its iteration: it brings the right degree and the right alphabet down to functions of $\varepsilon$ alone, while each loss in value and sensitivity stays explicit.
--
--   Differences from the source:
--   - reading: $\log|\Sigma_V|$ in $|V'|$, $\bar d_{U'}$ and item 3 (and in the code length) → $\log(2|\Sigma_V|)$; reason: obvious typo. As printed, item 3 is false at $|\Sigma_V|=1$ (INSIGHTS I1), and Lemma 5.4 on the next page writes $\log(2|\Sigma_V|)$.
--   - generalization: the fixed code of Proposition 5.1 and the expanders of Proposition 4.2 (one $H_D$ per degree $D$) → any code of relative distance $1-(\varepsilon/4)^3$ with $k\le K\varepsilon^{-6}\log(2|\Sigma_V|)$, for every $K>0$, and any per-vertex expanders of degree $d_\varepsilon$ with $\lambda\le\sqrt\varepsilon$; the right alphabet is then the code's alphabet, and its size bound $O(\varepsilon^{-6})$ is Proposition 5.1's guarantee for its code; reason: the paper's choices are one instance, so the statement specializes to the paper's.
--   - generalization: "sufficiently large absolute constants $c_{AR},C_{red}$" → every $c_{AR}\ge c_0$, with $C_{red}$ and the other constants depending on $c_{AR}$ and $K$ only; reason: it specializes to the paper's choice of $c_{AR}$ and rules out a degree $d_\varepsilon$ too small for any expander with $\lambda\le\sqrt\varepsilon$.
--   - reading: every $O(\cdot)$, $\Theta(\cdot)$ → explicit constants $C_V,C_U,c,C$ fixed before $\varepsilon$ and the family; reason: absolute constants, as in the paper's proof.
--   - encoding: $|U'|=n$ → by construction (the reduced graph's left vertex set is $U$); $\mathrm{SwapDist}(I,\tilde I)$ on the right of item 3 → the bound for every swap path of length $n$ from $I$ to $\tilde I$; deterministic $\pi'$ in items 4–5 → point masses; reason: equivalent forms.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), pp. 28–29 (PDF 31–32), Lemma 5.3

import Mathlib
import Definitions.Def_SensLabelCover_DH_AlphabetReduction

namespace SensLabelCover.DH

/-- Lemma 5.3 (Alphabet-then-degree reduction), pp. 28–29 (PDF pp. 31–32), with `log(2|Σ_V|)`
for the printed `log |Σ_V|` (INSIGHTS I1), for every sufficiently large `c_AR`, every code of
relative distance `1 − (ε/4)³` with block length `k ≤ K ε^{−6} log(2|Σ_V|)`, and every
`[D, d_ε, λ]`-expanders with `λ ≤ √ε` and incidence orderings (the paper's explicit choices from
Propositions 4.2 and 5.1 are one instance). `|V| = m`, `d̄_V = |E|/m`, `d̄_U = |E|/n`,
`Δ_U = G.maxLDeg`, `δ_V = G.minRDeg`. Every `O(·)`/`Θ(·)` is an explicit constant. -/
theorem lemma_5_3 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ cAR : ℝ, c₀ ≤ cAR → ∀ K : ℝ, 0 < K →
    ∃ Cred CV CU cdeg Cdeg : ℝ, 0 < Cred ∧ 0 < CV ∧ 0 < CU ∧ 0 < cdeg ∧ 0 < Cdeg ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 16 →
    ∀ {U V E SU SV : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
      [Fintype E] [DecidableEq E] [Fintype SU] [DecidableEq SU] [Fintype SV] [DecidableEq SV]
      (G : BGraph U V E) (hD : ∀ v, 0 < G.rdeg v) (𝓘 : Set (LCInst U E SU SV)),
      SwapClosed lcAdj 𝓘 →
    ∀ {k : ℕ} {SH : Type} [Fintype SH] [DecidableEq SH] (C : SV → Fin k → SH),
      IsCode C ((ε / 4) ^ 3) →
      (k : ℝ) ≤ K * ε⁻¹ ^ 6 * Real.log (2 * (Fintype.card SV : ℝ)) →
    ∀ dr : DRData (arGraph G k) (dEps cAR ε), (∀ w, IsExpander (dr.nb w) (Real.sqrt ε)) →
      ((Fintype.card (DRV (arGraph G k)) : ℝ) ≤
          CV * ε⁻¹ ^ 6 * (Fintype.card V : ℝ) *
            ((Fintype.card E : ℝ) / (Fintype.card V : ℝ)) * Real.log (2 * (Fintype.card SV : ℝ))) ∧
      ((Fintype.card (DRE (arGraph G k) (dEps cAR ε)) : ℝ) / (Fintype.card U : ℝ) ≤
          CU * ((Fintype.card E : ℝ) / (Fintype.card U : ℝ)) * ε⁻¹ ^ 7 *
            Real.log (2 * (Fintype.card SV : ℝ))) ∧
      (∀ x, (redGraph dr).rdeg x = dEps cAR ε) ∧
      cdeg / ε ≤ (dEps cAR ε : ℝ) ∧ (dEps cAR ε : ℝ) ≤ Cdeg / ε ∧
      (∀ I ∈ 𝓘, lcSat G I → lcSat (redGraph dr) (red C dr I)) ∧
      (∀ I ∈ 𝓘, ∀ μ : PMF (Assignment U (DRV (arGraph G k)) SU SH),
        4 * Real.sqrt ε ≤ expect μ (lcVal (redGraph dr) (red C dr I)) →
          ε ≤ expect (μ.bind (redRecover G k hD I)) (lcVal G I)) ∧
      (∀ I ∈ 𝓘, ∀ I' ∈ 𝓘, ∀ n : ℕ, SwapPath lcAdj n I I' →
        SwapDistLE lcAdj (red C dr I) (red C dr I')
          (Cred * ε⁻¹ ^ 7 * Real.log (2 * (Fintype.card SV : ℝ)) * n)) ∧
      (∀ I ∈ 𝓘, ∀ π π' : Assignment U (DRV (arGraph G k)) SU SH,
        emd lcDist (redRecover G k hD I π) (redRecover G k hD I π') ≤
          (1 + (G.maxLDeg : ℝ) / (G.minRDeg : ℝ)) * lcDist π π') ∧
      (∀ I ∈ 𝓘, ∀ I' ∈ 𝓘, lcAdj I I' → ∀ π : Assignment U (DRV (arGraph G k)) SU SH,
        emd lcDist (redRecover G k hD I π) (redRecover G k hD I' π) ≤ 1 / (G.minRDeg : ℝ)) := by sorry

end SensLabelCover.DH
