-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_3_1
-- name    : SuperlatSVP.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:25.184045+00:00
-- url     : https://prove2.me/theorems/98ea7631-4702-4c95-8400-a7621740d836
-- title:
--   Lemma 3.1 — $\mathbb E_z\rho_{1/t}(L_z^*\setminus\{0\})\le 2\rho_{1/t}(L^*)/p$
-- statement:
--   Let $L=B\mathbb Z^n$ be a full-rank lattice and $p$ a prime. For $z\in\mathbb F_p^n\setminus\{0\}$ let $L_z=L+\mathbb Z\,B\bar z/p$ be the index-$p$ extension, and let $\mathbb E_z$ denote the average over a uniformly random nonzero $z$. Then for every $t>0$,
--   $$\mathbb E_z\,\rho_{1/t}(L_z^*\setminus\{0\})\le\frac{2\,\rho_{1/t}(L^*)}{p},$$
--   where $L^*=\{y:\langle y,x\rangle\in\mathbb Z\ \forall x\in L\}$ is the dual lattice.
--
--   A random index-$p$ extension therefore reduces the nonzero dual Gaussian mass by the factor $p$, up to a factor $2$. This is how the first superlattice $\Gamma_0$ is made smooth at the prescribed width.
--
--   Differences from the source:
--   - encoding: any integer representative z̄ and real-valued expectations → the representative ZMod.val and averages in [0,∞]; reason: L_z does not depend on the representative, and the masses are finite
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §3, p.24 (PDF p.24), Lemma 3.1, eq. (3.3)

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_indexExt
import Definitions.Def_RegevLWE_GaussConv_Lattice

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma 3.1 (Non-zero Gaussian mass of index-p extensions). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §3, p.24 (PDF p.24). Setting of
§3: "Let L = BZⁿ be a full-rank lattice and p a prime", `L_z = L + ℤBz̄/p` (3.1), and the expectation
"is over a uniform random nonzero z ∈ F_pⁿ". Statement: "For every t > 0,
E_z ρ1/t(L∗z ∖ {0}) ≤ 2ρ1/t(L∗)/p. (3.3)"

**Formalization Note.** `L*` is the published `RegevLWE.GaussConv.dual`; `E_z` is `zAvg`, the average
over the `pⁿ − 1` nonzero `z`; masses in `ℝ≥0∞`. -/
theorem lemma_3_1 (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (p : ℕ)
    [Fact p.Prime] (t : ℝ) (ht : 0 < t) :
    zAvg (fun z : Fin n → ZMod p =>
        rhoSet (1 / t) ((RegevLWE.GaussConv.dual (indexExt B p z) : Set (E n)) \ {0})) ≤
      2 * rhoSet (1 / t) (RegevLWE.GaussConv.dual (lat B) : Set (E n)) / (p : ℝ≥0∞) := by sorry

end SuperlatSVP
