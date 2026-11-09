-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_1
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:42.153504+00:00
-- url     : https://prove2.me/theorems/ad305b50-fcbe-4cec-af6a-d80fbf9d4dcd
-- title:
--   Lemma A.1 — Public parameter choice
-- statement:
--   Fix target smoothing $\gamma>0$, rates $0<\kappa_{min}<\kappa_{max}<\alpha_\gamma$, a fixed $C_H>0$, a prescribed separation factor $K>0$, and natural polynomial exponents $a,b,e$. There exist $C\ge1$ and $d_0\ge2$ such that for every $d\ge d_0$ and budgets $1\le P\le d^a$, $d^{-b}\le\varepsilon\le1$, $d^{-e}\le\rho\le1/10$, all positive, there are a layout and sizes $n_j$ with $m=\lfloor d/B\rfloor$ and $d_{pad}=d-Bm$. Each size is a valid power of two and each rate $\kappa_j=\log(n_j)/m$ lies in the fixed interval. With $H=C_H\log(dP/(\varepsilon\rho))$, one has
--   $$ B\asymp(d/\log d)^{1/3},\quad m\asymp d^{2/3}(\log d)^{1/3},\quad H\asymp\log d,\quad N_d=2^{d_{pad}}\prod_jn_j=\exp(\Theta(d)). $$
--   The same envelope $C$ bounds both sides of each comparison, uniformly over $d$ and the allowed budgets. Adjacent gaps are at least $(\kappa_{max}-\kappa_{min})/(2B)$ and exceed $K(\sqrt{H/m}+H/m)$. Moreover $m\ge\max\{2,\sqrt2\gamma\}$ and, for $c_0=(\alpha_\gamma-\kappa_{max})/2$,
--   $$\gamma^{-1}\sqrt{8\log(1/\zeta(\gamma))/m}\le c_0,\qquad \zeta(\gamma),e^{-c_0m}\le\rho^2/100,\qquad RPB\delta\le\rho^2/(100d)\ (R<B).$$
--   This supplies the full public arithmetic choice, independently of the instance and algorithm.
--
--   Differences from the source:
--   - encoding: d coordinates in B consecutive blocks and d−Bm padding coordinates, m=⌊d/B⌋ → Layout with d=B*m+pad and an explicit hypothesis m=d/B when the source uses that convention; reason: this labels the same coordinates; padding may be zero and the empty product is one
--   - encoding: Theta and exp(Theta(d)) in (14) and the cardinality claim → one uniform envelope C and one threshold d0 for all displayed two-sided bounds; reason: finitely many positive comparison constants can be replaced by one C at least one without changing any asymptotic statement
--   - generalization: fixed polynomial budgets and H from (13) with a sufficiently large constant → all budgets in fixed polynomial envelopes and every fixed positive C_H; reason: the arithmetic proof uses only the envelopes and H=Theta(log d); the source choices are included
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.1, p. 19

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

/-- Full arithmetic parameter choice, including arbitrary prescribed rate-gap factor K.
The same positive envelope constant C bounds every Theta in (14) and log N. -/
theorem lemma_A_1 (γ κmin κmax C_H K : ℝ) (hγ : 0 < γ)
    (hκmin : 0 < κmin) (hκ : κmin < κmax) (hκmax : κmax < informationLevel 1 γ)
    (hCH : 0 < C_H) (hK : 0 < K) (a b e : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧
    ∀ d : ℕ, d₀ ≤ d → ∀ P : ℕ, 1 ≤ P → P ≤ d ^ a →
    ∀ ε ρ : ℝ, 0 < ε → (d : ℝ) ^ (-(b : ℤ)) ≤ ε → ε ≤ 1 →
      0 < ρ → (d : ℝ) ^ (-(e : ℤ)) ≤ ρ → ρ ≤ 1/10 →
    ∃ L : Layout, ∃ n : Fin L.B → ℕ,
      L.d = d ∧ L.m = d / L.B ∧ L.pad = d - L.B * L.m ∧
      2 ≤ L.m ∧ Real.sqrt 2 * γ ≤ L.m ∧ L.sizesValid n ∧
      (∀ j, ∃ k : ℕ, n j = 2 ^ k) ∧
      (∀ j, κmin ≤ rate L.m (n j) ∧ rate L.m (n j) ≤ κmax) ∧
      (∀ j k : Fin L.B, k.val = j.val + 1 →
        (κmax - κmin) / (2 * L.B) ≤ rate L.m (n k) - rate L.m (n j)) ∧
      L.separated n (L.publicH P ε ρ C_H) K ∧
      (d / Real.log d : ℝ) ^ (1/3 : ℝ) / C ≤ L.B ∧
      (L.B : ℝ) ≤ C * (d / Real.log d : ℝ) ^ (1/3 : ℝ) ∧
      ((d : ℝ) ^ (2/3 : ℝ) * Real.log d ^ (1/3 : ℝ)) / C ≤ L.m ∧
      (L.m : ℝ) ≤ C * ((d : ℝ) ^ (2/3 : ℝ) * Real.log d ^ (1/3 : ℝ)) ∧
      Real.log d / C ≤ L.publicH P ε ρ C_H ∧
      L.publicH P ε ρ C_H ≤ C * Real.log d ∧
      Real.exp (d / C) ≤ (2 ^ L.pad * ∏ j, n j : ℕ) ∧
      ((2 ^ L.pad * ∏ j, n j : ℕ) : ℝ) ≤ Real.exp (C * d) ∧
      Real.sqrt (8 * Real.log (1 / gateBudget L.m L.B ε ρ γ) / L.m) / γ ≤
        (informationLevel 1 γ - κmax) / 2 ∧
      gateBudget L.m L.B ε ρ γ ≤ ρ ^ 2 / 100 ∧
      Real.exp (-((informationLevel 1 γ - κmax) / 2) * L.m) ≤ ρ ^ 2 / 100 ∧
      ∀ R : ℕ, R < L.B → (R * P * L.B : ℝ) * hidingBudget d P ρ ≤ ρ ^ 2 / (100 * d) := by sorry

end ParallelDiffusionLB.NearIsotropic
