-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_8
-- name    : PrivRobustStat.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:27.836431+00:00
-- url     : https://prove2.me/theorems/c815895e-743c-4f5e-a957-07bda4bd7b27
-- title:
--   Lemma 8, p.21 — Algorithm 3 loses at most $\alpha/(100T)$ good weight and $\sum_{i\in G}\bar w_ig_i\le\kappa/400$
-- statement:
--   **Lemma 8.** Let $x_{[n]}$, $c$, $M_i=(x_i-c)(x_i-c)^\top$, $w\in[0,\tfrac1n]^n$, $G\subseteq[n]$, $\kappa,\alpha>0$, $T\ge1$, and suppose $\hat\Sigma(w_G)=\sum_{i\in G}w_iM_i\preceq\frac\kappa{400}I$. Run Algorithm 3 with $\tau_{\max}=T(p+1)\kappa/(4\alpha)$, let $(\bar w,Z)$ be its output and $g_i=\operatorname{Tr}(Z^\top M_iZ)/\|Z\|_F^2$ ($g_i=0$ if $Z=0$). Then, for every realization of the Gaussian draws,
--
--   $$\|[w-\bar w]_G\|_1\le\frac{\alpha}{100T},\qquad \sum_{i\in G}\bar w_ig_i\le\frac\kappa{400}.\tag{21}$$
--
--   Differences from the source:
--   - generalization: p and r as in Algorithm 1 → any depth p and sketch dimension r; reason: the proof uses only the formula for τ_max; Algorithm 1's p, r are particular values
--   - encoding: the conclusion of Lemma 8 (no probability) → holds for every realization of Algorithm 3's Gaussian draws; reason: the lemma is deterministic
--   - encoding: T ∈ ℕ → T ≥ 1; reason: τ_max > 0 is Algorithm 3's input condition
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 8, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_PrivRobustStat_Filter

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 8**, p.21 (PDF p.24).

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Suppose that Σ̂(w_G) ⪯ κ/400 I, i.e., Item (b) of Proposition 1 holds. Let (w̄, Z) be returned by
Algorithm 3, and let τ_max := T(p+1)κ/(4α) and g_i := Tr(Z⊤M_iZ)/∥Z∥²_F for all i ∈ [n], as in
Algorithm 1. Then ∥[w − w̄]_G∥₁ ≤ α/(100T), ∑_{i∈G} w̄_ig_i ≤ κ/400. (21)"

**Formalization Note.** §3 setting: dataset `x[n]`, public centre `c`, `M_i = (x_i − c)(x_i − c)⊤`,
`Σ̂(u) = ∑_i u_iM_i = covC x u c`. The claim is deterministic: it holds for every realization `g` of
Algorithm 3's Gaussian draws, for every sketch dimension `r` and every depth `p`. Inputs:
`w ∈ [0, 1/n]^n`, `κ, α > 0`, `T ≥ 1` (so that `τ_max > 0`, Algorithm 3's input condition), any
`G ⊆ [n]`. `g_i := 0` if `Z = 0` (Algorithm 1, Line 6). -/
theorem lemma_8 {d n r : ℕ} (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ) (hw : InBox n w)
    (G : Finset (Fin n)) (κ α : ℝ) (hκ : 0 < κ) (hα : 0 < α) (T p : ℕ) (hT : 1 ≤ T)
    (hb : ((κ / 400) • (1 : Matrix (Fin d) (Fin d) ℝ) - covC x (restrict w G) c).PosSemidef)
    (g : ℕ × ℕ × Fin d × Fin r → ℝ) :
    l1 (restrict (w - a3weights x c w κ ((T : ℝ) * ((p : ℝ) + 1) * κ / (4 * α)) p g) G) ≤
        α / (100 * (T : ℝ)) ∧
      ∑ i ∈ G, a3weights x c w κ ((T : ℝ) * ((p : ℝ) + 1) * κ / (4 * α)) p g i *
          score (a3Z x c w κ ((T : ℝ) * ((p : ℝ) + 1) * κ / (4 * α)) p g) (outer (x i - c)) ≤
        κ / 400 := by sorry

end PrivRobustStat
