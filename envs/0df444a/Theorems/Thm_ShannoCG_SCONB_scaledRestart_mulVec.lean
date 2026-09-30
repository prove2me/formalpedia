-- Prove2me | Theorems.Thm_ShannoCG_SCONB_scaledRestart_mulVec
-- name    : ShannoCG.SCONB.scaledRestart_mulVec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T07:23:25.765565+00:00
-- url     : https://prove2.me/theorems/12e87f9b-4b5f-4902-997b-52c91ebfb255
-- title:
--   Eq. (38), corrected: the self-scaled restart matrix applied to a vector
-- statement:
--   Let $p_t, y_t \in \mathbb R^n$ with $p_t' y_t \ne 0$, let $\gamma_t = p_t'y_t / y_t'y_t$ and let $\hat H_k$ be the self-scaled restart matrix (37). Then for every $g \in \mathbb R^n$
--
--   $$\hat H_k g = \frac{p_t' y_t}{y_t' y_t}\, g - \frac{p_t' g}{y_t' y_t}\, y_t + \left(2\,\frac{p_t' g}{p_t' y_t} - \frac{y_t' g}{y_t' y_t}\right) p_t.$$
--
--   The paper prints this identity for $g = g_{k+1}$ as (38) with coefficient $\frac{p_t'g_{k+1}}{p_t'y_t} - \frac{y_t'g_{k+1}}{y_t'y_t}$ on $p_t$, without the factor $2$. Expanding (37) gives the factor $2$, as in the paper's own (39), which is this identity with $g = y_k$. The printed and corrected versions agree when $p_t'g_{k+1} = 0$, the only case the paper uses.
--
--   **Formalization Note** The corrected identity is stated for an arbitrary vector $g$. The hypothesis $p_t'y_t \ne 0$ is needed: without it Lean's total division makes the two sides differ.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 250 (PDF p. 7), §IV, eq. (38) (corrected: factor 2 on the p_t'g_{k+1}/p_t'y_t term, as in eq. (39))

import Mathlib
import Definitions.Def_ShannoCG_SCONB_gammaScale
import Definitions.Def_ShannoCG_SCONB_scaledRestart

open Matrix

namespace ShannoCG.SCONB

/-- Shanno, *Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV, p. 250 (PDF 7), eq. (38), **corrected**: for the self-scaled restart matrix (37),
`Ĥ_k g = (p_t'y_t / y_t'y_t) g − (p_t'g / y_t'y_t) y_t + (2 p_t'g / p_t'y_t − y_t'g / y_t'y_t) p_t`.

The paper prints the coefficient of `p_t` as `p_t'g_{k+1}/p_t'y_t − y_t'g_{k+1}/y_t'y_t`, without the
factor `2`; expanding (37) gives the `2`, exactly as in the paper's own (39) (which is this identity
with `g = y_k`). The two versions agree when `p_t'g_{k+1} = 0`, the only case the paper uses (42).

**Formalization Note.** Stated for an arbitrary vector `g` (the paper's `g_{k+1}`; with `g = y_k` it is
(39)). The hypothesis `p_t ⬝ᵥ y_t ≠ 0` is needed: when it fails, Lean's total division makes the
two sides differ. -/
theorem scaledRestart_mulVec {n : ℕ} (pt yt g : Fin n → ℝ) (hpy : pt ⬝ᵥ yt ≠ 0) :
    scaledRestart pt yt *ᵥ g =
      gammaScale pt yt • g - ((pt ⬝ᵥ g) / (yt ⬝ᵥ yt)) • yt
        + (2 * ((pt ⬝ᵥ g) / (pt ⬝ᵥ yt)) - (yt ⬝ᵥ g) / (yt ⬝ᵥ yt)) • pt := by sorry

end ShannoCG.SCONB
