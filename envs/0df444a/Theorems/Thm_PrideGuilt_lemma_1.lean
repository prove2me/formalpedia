-- Prove2me | Theorems.Thm_PrideGuilt_lemma_1
-- name    : PrideGuilt.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:58:08.552007+00:00
-- url     : https://prove2.me/theorems/e600fdbf-54cb-4e85-9748-7a06511cad87
-- title:
--   Lemma 1 — the evolutionarily stable recycling rate (corrected: no stable equilibrium at $f=c_r-\gamma_P$, $c_r-\gamma_G$ when $\gamma_P>\gamma_G$)
-- statement:
--   Assume the standing assumptions, $\gamma_P>0$, $\gamma_G>0$ and $\gamma_P\ne\gamma_G$, and let $c_r=c_e-I_P-I_G$ and $\tau_m(f)=(f-c_r+\gamma_P)/(\gamma_P-\gamma_G)$. For every reward $f$, the stable equilibria of Definition 1 are as follows.
--
--   1. **(i)** If $f<c_r-\max(\gamma_P,\gamma_G)$, or $\gamma_G>\gamma_P$ and $f=c_r-\gamma_G$, the only stable equilibrium is $\tau=0$.
--   2. **(iii)** If $f>c_r-\min(\gamma_P,\gamma_G)$, or $\gamma_G>\gamma_P$ and $f=c_r-\gamma_P$, the only stable equilibrium is $\tau=1$.
--   3. **(iv)** If $\gamma_P>\gamma_G$ and $c_r-\gamma_P<f<c_r-\gamma_G$, the only stable equilibrium is $\tau=\tau_m(f)$.
--   4. **(ii)** If $\gamma_G>\gamma_P$ and $c_r-\gamma_G<f<c_r-\gamma_P$, the stable equilibria are exactly $\tau=0$ and $\tau=1$; moreover, for $\tau\in[0,1]$,
--   $$
--   U_R(f,\tau)>U_N(\tau)\iff \tau>\tau_m(f),\qquad U_R(f,\tau)<U_N(\tau)\iff \tau<\tau_m(f),
--   $$
--   so the evolutionary dynamic ("$\tau$ increases (decreases) when $U_R>(<)U_N$") leads to $1$ from $\tau^0>\tau_m(f)$ and to $0$ from $\tau^0<\tau_m(f)$.
--   5. $\tau_m(f)\in(0,1)$ whenever $c_r-\max(\gamma_P,\gamma_G)<f<c_r-\min(\gamma_P,\gamma_G)$.
--   6. If $\gamma_P>\gamma_G$ and $f\in\{c_r-\gamma_P,\,c_r-\gamma_G\}$, there is no stable equilibrium.
--   7. At every other reward, the Lemma 1 rate $\tau^*(f)$ is a stable equilibrium.
--
--   The lemma tells the manufacturer which community recycling rate a reward induces: nobody recycles for low rewards, everybody for high ones, an interior share when pride dominates guilt and the reward is moderate, and a bandwagon to one of the extremes when guilt dominates.
--
--   Differences from the source:
--   - correction: (i) τ*(f) = 0 for f ≤ c_r − max(γP, γG) and (iii) τ*(f) = 1 for f ≥ c_r − min(γP, γG), including the endpoints → when γP > γG the endpoints f = c_r − γP and f = c_r − γG are excluded from (i) and (iii), and no stable equilibrium exists there; reason: at γP = 2, γG = 1, c_e = 3, I_P = I_G = 0, f = 1 = c_r − γP we have U_R(f,0) = U_N(0) = 0, so the strict inequality of Definition 1(ii) fails, U_R(f,1) = −2 < −1 = U_N(1) and τ_m(f) = 0, so no case of Definition 1 holds
--   - reading: (ii) τ*(f) = 1 if τ^0 ≥ τ_m(f), 0 if τ^0 < τ_m(f) → the stable equilibria are exactly {0, 1}, and on [0, 1] U_R − U_N has the sign of τ − τ_m(f); reason: Definition 1 has no dynamics; the selection by τ^0 is the dynamic of p.9 (τ increases when U_R > U_N), which is what the sign statement expresses; at τ^0 = τ_m(f) both utilities are equal and the printed choice is a convention kept in the definition tauStar
--   - encoding: the evolutionarily stable equilibrium τ*(f) is given by (i)–(iv) → each case characterizes the set of stable equilibria of Definition 1 by an iff, and the Lemma 1 formula tauStar is shown to be a stable equilibrium off the two corrected endpoints; reason: Definition 1 is the paper's notion of stable equilibrium; the formula is a definition used by §4
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Lemma 1, p.9 (with Definition 1, p.8)

import Mathlib
import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_IsStableEq
import Definitions.Def_PrideGuilt_tauStar

namespace PrideGuilt

/-- **Lemma 1 (the evolutionarily stable recycling rate), corrected at two endpoints.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Lemma 1, p.9 (PDF 10), with Definition 1, p.8 (PDF 9).

Under the standing assumptions, with `γ_P, γ_G > 0`, `γ_P ≠ γ_G` and `c_r = c_e − I_P − I_G`,
for every reward `f`:
(i) if `f < c_r − max(γ_P, γ_G)`, or `γ_G > γ_P` and `f = c_r − γ_G`, the stable equilibria
  (Definition 1) at `f` are exactly `τ = 0`;
(iii) if `f > c_r − min(γ_P, γ_G)`, or `γ_G > γ_P` and `f = c_r − γ_P`, they are exactly `τ = 1`;
(iv) if `γ_P > γ_G` and `c_r − γ_P < f < c_r − γ_G`, they are exactly `τ = τ_m(f)`;
(ii) if `γ_G > γ_P` and `c_r − γ_G < f < c_r − γ_P`, they are exactly `τ ∈ {0, 1}`, and on
  `[0, 1]` `U_R > U_N` iff `τ > τ_m(f)` and `U_R < U_N` iff `τ < τ_m(f)` (the evolutionary
  dynamic, which selects `1` from `τ⁰ > τ_m(f)` and `0` from `τ⁰ < τ_m(f)`);
(final clause) `τ_m(f) ∈ (0, 1)` for `c_r − max(γ_P, γ_G) < f < c_r − min(γ_P, γ_G)`;
(correction) if `γ_P > γ_G` and `f ∈ {c_r − γ_P, c_r − γ_G}`, no `τ` is a stable equilibrium;
(selection) at every other `f` the Lemma 1 rate `τ*(f)` (`tauStar`) is a stable equilibrium.

**Formalization Note.** Correction: at `γ_P = 2`, `γ_G = 1`, `c_e = 3`, `I_P = I_G = 0`, `f = 1 = c_r − γ_P`
we have `U_R|_{τ=0} = U_N|_{τ=0} = 0`, so the strict inequality of Definition 1(ii) fails, and
neither (i) nor (iii) holds; the printed Lemma 1(i) assigns `τ* = 0` there. Reading: Definition 1
has no dynamics; case (ii)'s selection by `τ⁰` is stated through the sign of `U_R − U_N`, which is
the dynamic of p.9. -/
theorem lemma_1 (P : Params) (hP : Standing P) (γP γG : ℝ) (hγP : 0 < γP) (hγG : 0 < γG)
    (hne : γP ≠ γG) (f : ℝ) :
    ((f < cr P - max γP γG ∨ (γP < γG ∧ f = cr P - γG)) →
        ∀ τ : ℝ, IsStableEq P γP γG f τ ↔ τ = 0) ∧
    ((cr P - min γP γG < f ∨ (γP < γG ∧ f = cr P - γP)) →
        ∀ τ : ℝ, IsStableEq P γP γG f τ ↔ τ = 1) ∧
    ((γG < γP ∧ cr P - γP < f ∧ f < cr P - γG) →
        ∀ τ : ℝ, IsStableEq P γP γG f τ ↔ τ = tauM P γP γG f) ∧
    ((γP < γG ∧ cr P - γG < f ∧ f < cr P - γP) →
        (∀ τ : ℝ, IsStableEq P γP γG f τ ↔ (τ = 0 ∨ τ = 1)) ∧
        ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
          ((UN P γG τ < UR P γP f τ ↔ tauM P γP γG f < τ) ∧
           (UR P γP f τ < UN P γG τ ↔ τ < tauM P γP γG f))) ∧
    ((cr P - max γP γG < f ∧ f < cr P - min γP γG) →
        0 < tauM P γP γG f ∧ tauM P γP γG f < 1) ∧
    ((γG < γP ∧ (f = cr P - γP ∨ f = cr P - γG)) → ∀ τ : ℝ, ¬ IsStableEq P γP γG f τ) ∧
    (¬ (γG < γP ∧ (f = cr P - γP ∨ f = cr P - γG)) →
        IsStableEq P γP γG f (tauStar P γP γG f)) := by sorry

end PrideGuilt
