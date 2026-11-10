-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_4_2
-- name    : SuperlatSVP.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:45.147577+00:00
-- url     : https://prove2.me/theorems/35343aae-0579-493f-b21a-0b605069e880
-- title:
--   Lemma 4.2 — shell-count estimates $\mathbb EK_L^2/(pm_L^2)\le O(n^{3/2})q^{-1}$ and $\mathrm{Var}\,K_{L/p}/m_{L/p}^2\le O(n^5)q^{-2}$
-- statement:
--   Assume the standing setting of §4.1 ($\det L=1$, (2.3) with $b=2^\beta\ge\sqrt{4/3}$ absorbed, $\lambda_1(L)\le\lambda\le(1+n^{-2})\lambda_1(L)$, and a prime $p$ in the range (4.7)). For a full-rank lattice $\Lambda$ let $K_\Lambda(u)=\#((\Lambda+u)\cap A)$ be the number of points of $\Lambda+u$ in the midpoint shell $A$, and let $m_\Lambda=\operatorname{vol}(A)/\det\Lambda$. Expectations and variances are over $u$ uniform modulo $\Lambda$. Then
--   $$\frac{\mathbb EK_L^2}{p\,m_L^2}\le O(n^{3/2})\,q^{-1},\qquad \frac{\operatorname{Var}K_{L/p}}{m_{L/p}^2}\le O(n^5)\,q^{-2}.$$
--
--   These two bounds feed Lemma 4.3: averaged over the random extension, the midpoint-shell count of $\Gamma_0$ has small relative variance.
--
--   **Formalization Note** The $O(\cdot)$ constants are one absolute constant $C$, and the bounds hold for $n\ge n_0$, both chosen before the instance. $L/p$ is the lattice $\tfrac1pB\,\mathbb Z^n$.
--
--   Differences from the source:
--   - encoding: O(·) and the implicit large-n regime → ∃ C ∃ n₀ ∀ n ≥ n₀, chosen before the instance; reason: the source's asymptotic constants are uniform over the related parameters (p.14)
--   - encoding: a ratio and a variance of real random variables → the first bound multiplied out, and Var X ≤ c written E X² ≤ (E X)² + c, in [0,∞]; reason: the means are finite, so the statements are equivalent
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.1.1, p.32 (PDF p.32), Lemma 4.2

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_shellA
import Definitions.Def_SuperlatSVP_Sec41Setting
import Definitions.Def_SuperlatSVP_unifMean

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma 4.2 (Shell-count estimates). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.1.1, p.32 (PDF p.32): "We have
EK²_L/(p m²_L) ≤ O(n^{3/2})q^{−1},   Var K_{L/p}/m²_{L/p} ≤ O(n⁵)q^{−2}."
Here `K_Λ(u) = #((Λ + u) ∩ A)`, `m_Λ = vol(A)/det Λ` (4.8), and "Expectations and variances of K_Λ
are taken over u uniform modulo Λ". The setting is the §4.1 standing assumptions (`Sec41Setting`).

**Formalization Note.** `O(·)` is one absolute constant `C`, and the bounds hold for `n ≥ n₀`, both
chosen before the instance (p.14: "All the constants in the asymptotic notations … are uniform over
the related parameters"). `L/p = ((1/p)B)ℤⁿ`. In `ℝ≥0∞`: the first bound is multiplied out, and
`Var X ≤ c` is written `E X² ≤ (E X)² + c`. -/
theorem lemma_4_2 :
    ∃ (C : ℝ) (n₀ : ℕ), ∀ n : ℕ, n₀ ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℝ) (lam β : ℝ) (p : ℕ),
      p.Prime → Sec41Setting n B lam β p →
        unifMean B (fun u => shiftCount (lat B) (shellA n lam) u ^ 2) ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (3 / 2 : ℝ) / (chainQ n : ℝ)) * (p : ℝ≥0∞) *
              shellMass n lam B ^ 2 ∧
          unifMean ((1 / (p : ℝ)) • B)
              (fun u => shiftCount (lat ((1 / (p : ℝ)) • B)) (shellA n lam) u ^ 2) ≤
            unifMean ((1 / (p : ℝ)) • B)
                (fun u => shiftCount (lat ((1 / (p : ℝ)) • B)) (shellA n lam) u) ^ 2 +
              ENNReal.ofReal (C * (n : ℝ) ^ 5 / (chainQ n : ℝ) ^ 2) *
                shellMass n lam ((1 / (p : ℝ)) • B) ^ 2 := by sorry

end SuperlatSVP
