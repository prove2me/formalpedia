-- Prove2me | Theorems.Thm_ProdMomentConc_azuma_Lk
-- name    : ProdMomentConc.azuma_Lk
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:21.924744+00:00
-- url     : https://prove2.me/theorems/e72824c4-1e74-43c6-9ac6-01e891aea42d
-- title:
--   §A.2 — Azuma's inequality for the neighbourhood size $L_k$
-- statement:
--   Let every output read at most $\Delta_R$ underlying variables, let $1 \le k \le n$, let $I$ be a uniformly random $k$-subset of $[n]$, and let $L_k$ be the number of underlying variables read by the outputs in $I$. Then for every $\varepsilon > 0$,
--
--   $$
--   \Pr[L_k - \mathbb E L_k > \varepsilon] \le \exp\Big(-\frac{\varepsilon^2}{2k\Delta_R^2}\Big),
--   $$
--
--   and for every real threshold $r$,
--
--   $$
--   \Pr[L_k > r] \le \exp\Big(-\frac{(r - \mathbb E[L_k])_+^2}{2k\Delta_R^2}\Big).
--   $$
--
--   In the paper these follow from Azuma's inequality for the Doob martingale obtained by exposing the elements of $I$ one at a time, each of which changes $L_k$ by at most $\Delta_R$. They give the first of the two estimates of $\varepsilon_L$ in Lemma A.2 (ii).
--
--   **Formalization Note** $L_k$ is `Lk P I` with $I \sim$ `kSubsetLaw n k`; $\mathbb E L_k$ is the integral of this bounded function; $(x)_+ = \max(x, 0)$. The martingale is proof machinery and does not appear in the statement.
--
--   Differences from the source:
--   - generalization: r is the independence parameter of Theorem 3.4 (a natural number with 1 ≤ r ≤ m, r ≥ Δ_R), in the full setting of Theorem 3.5 → r any real number, and only the right-degree bound and 1 ≤ k ≤ n assumed; reason: L_k and its law depend only on the graph; the source's instance is r natural with its hypotheses
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), §A.2 (proof of Lemma A.2 (ii)), p.35 (PDF p.35)

import Mathlib
import Definitions.Def_ProdMomentConc_kSubsetLaw
import Definitions.Def_ProdMomentConc_Lk

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **Azuma estimate for the neighbourhood size `L_k`** (§A.2).
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), §A.2 (proof of Lemma A.2 (ii)), p.35.

If every output reads at most `ΔR` underlying variables and `I` is a uniformly random `k`-subset
of `[n]` (`1 ≤ k ≤ n`), then for every `ε > 0`, `Pr[L_k − E L_k > ε] ≤ exp(−ε²/(2kΔR²))`, and
for every threshold `r`, `Pr[L_k > r] ≤ exp(−(r − E[L_k])₊²/(2kΔR²))`.

**Formalization Note.** `L_k = Lk P I` with `I ∼ kSubsetLaw n k`; `E L_k` is the Bochner integral
of the bounded function `Lk P` against this finite measure. `(x)₊ = max x 0`. The threshold `r`
is any real number (in the paper it is the independence parameter). The Doob martingale of the
paper's proof is not part of the statement. -/
theorem azuma_Lk {m n : ℕ} (P : Fin n → Finset (Fin m)) (ΔR : ℕ)
    (hΔR : ∀ i, (P i).card ≤ ΔR) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (∀ ε : ℝ, 0 < ε →
      (kSubsetLaw n k).real
          {S | ε < (Lk P S : ℝ) - ∫ T, (Lk P T : ℝ) ∂(kSubsetLaw n k)} ≤
        Real.exp (-(ε ^ 2 / (2 * (k : ℝ) * (ΔR : ℝ) ^ 2)))) ∧
    (∀ r : ℝ,
      (kSubsetLaw n k).real {S | r < (Lk P S : ℝ)} ≤
        Real.exp (-((max (r - ∫ T, (Lk P T : ℝ) ∂(kSubsetLaw n k)) 0) ^ 2 /
          (2 * (k : ℝ) * (ΔR : ℝ) ^ 2)))) := by sorry

end ProdMomentConc
