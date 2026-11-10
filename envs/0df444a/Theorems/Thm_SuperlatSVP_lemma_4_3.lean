-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_4_3
-- name    : SuperlatSVP.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:14.176915+00:00
-- url     : https://prove2.me/theorems/41af5916-ce4b-4ca5-82ed-7cf383006c95
-- title:
--   Lemma 4.3 — with probability $\ge1-e^{-n^{1/4}}$ over $\Gamma_0$, every $\Lambda\supseteq\Gamma_0$ has $\mathrm{Var}\,K_\Lambda\le e^{-n^{1/4}}m_\Lambda^2$
-- statement:
--   Assume the standing setting of §4.1, with $p$ prime, and let $\Gamma_0=L+\mathbb Z\,B\bar z/p$ for $z$ uniform on $\mathbb F_p^n\setminus\{0\}$. Then for all sufficiently large $n$, with probability at least $1-e^{-n^{1/4}}$ over $\Gamma_0$, every full-rank lattice $\Lambda\supseteq\Gamma_0$ satisfies
--   $$\operatorname{Var}K_\Lambda\le e^{-n^{1/4}}\,m_\Lambda^2 .$$
--   Here $K_\Lambda(u)=\#((\Lambda+u)\cap A)$, $m_\Lambda=\operatorname{vol}(A)/\det\Lambda$, and the variance is over $u$ uniform modulo $\Lambda$.
--
--   This makes the midpoint-shell counts of every lattice in the superlattice chain $\Gamma_0\subseteq\dots\subseteq\Gamma_D$ concentrated, which is what controls the list moments of the algorithm.
--
--   **Formalization Note** The probability is the fraction of nonzero $z$ for which the conclusion holds. $\Lambda$ ranges over every lattice $B_\Lambda\mathbb Z^n$ with $\det B_\Lambda\ne0$ that contains $\Gamma_0$. One threshold $n_0$ is chosen before the instance.
--
--   Differences from the source:
--   - encoding: probability over Γ0 and "every Λ ⊇ Γ0" → the fraction of nonzero z, and every full-rank B_Λℤⁿ containing Γ0 with the mean taken through B_Λ; reason: Γ0 is determined by z, and the mean of a Λ-periodic count does not depend on the basis
--   - encoding: a variance and the implicit large-n regime → E K² ≤ (E K)² + e^{−n^{1/4}} m² in [0,∞], for n ≥ n₀ chosen before the instance; reason: the means are finite; asymptotic constants are uniform (p.14)
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.1.1, p.33 (PDF p.33), Lemma 4.3

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_shellA
import Definitions.Def_SuperlatSVP_Sec41Setting
import Definitions.Def_SuperlatSVP_unifMean
import Definitions.Def_SuperlatSVP_indexExt

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma 4.3 (Shell-count variance). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.1.1, p.33 (PDF p.33): "With probability at least
1 − e^{−n^{1/4}} over Γ0, every Λ ⊇ Γ0 satisfies Var KΛ ≤ e^{−n^{1/4}} m²_Λ."
Here `Γ0 = L + ℤBz̄/p` with `z` uniform on `F_pⁿ ∖ {0}` (p.32), and the setting is the §4.1
standing assumptions (`Sec41Setting`).

**Formalization Note.** The probability over `Γ0` is the fraction of nonzero `z` (`zAvg` of the
indicator). "Every Λ ⊇ Γ0" ranges over every full-rank lattice `Λ = B_Λℤⁿ` containing `Γ0`; the
mean over `u` uniform modulo `Λ` uses the basis `B_Λ`. `Var X ≤ c` is `E X² ≤ (E X)² + c` in
`ℝ≥0∞`. One threshold `n₀` before the instance. -/
theorem lemma_4_3 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℝ) (lam β : ℝ) (p : ℕ)
      [Fact p.Prime], Sec41Setting n B lam β p →
        ENNReal.ofReal (1 - Real.exp (-((n : ℝ) ^ (1 / 4 : ℝ)))) ≤
          zAvg (fun z : Fin n → ZMod p =>
            Set.indicator
              {z' : Fin n → ZMod p | ∀ BΛ : Matrix (Fin n) (Fin n) ℝ, BΛ.det ≠ 0 →
                indexExt B p z' ≤ lat BΛ →
                  unifMean BΛ (fun u => shiftCount (lat BΛ) (shellA n lam) u ^ 2) ≤
                    unifMean BΛ (fun u => shiftCount (lat BΛ) (shellA n lam) u) ^ 2 +
                      ENNReal.ofReal (Real.exp (-((n : ℝ) ^ (1 / 4 : ℝ)))) *
                        shellMass n lam BΛ ^ 2}
              1 z) := by sorry

end SuperlatSVP
