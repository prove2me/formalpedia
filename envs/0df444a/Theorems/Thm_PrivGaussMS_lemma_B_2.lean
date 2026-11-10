-- Prove2me | Theorems.Thm_PrivGaussMS_lemma_B_2
-- name    : PrivGaussMS.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:10:44.627757+00:00
-- url     : https://prove2.me/theorems/4d7f6438-3729-4709-bead-36e59027f0be
-- title:
--   Lemma B.2 — exact conditional resampling $X\overset d=1_n\bar X^T+US(X)^{1/2}$ given $(\bar X,S(X))$, and (13)
-- statement:
--   Let $n>\max\{m,d\}$ and $X\sim P^{\otimes n}$ for a nonsingular Gaussian $P=\mathcal N(\mu,\Sigma)$, $\Sigma\succ0$. Conditional on $(\bar X,S(X))$,
--   $$X\overset d=1_n\bar X^T+US(X)^{1/2},$$
--   where $U\in\mathbb R^{n\times d}$ is a uniform centered frame ($U^TU=I_d$, $1_n^TU=0$) independent of the statistics. Consequently, drawing a fresh $U$ and keeping the first $m$ rows gives distribution $P^{\otimes m}$ after averaging over $X$.
--
--   This exact resampling rule is what the correction preserves.
--
--   Differences from the source:
--   - reading: 'conditional on (X̄, S(X)), X =d 1X̄ᵀ + US^{1/2}, U independent of the statistics' → the joint law of (X̄, S(X), X) equals that of (X̄, S(X), 1X̄ᵀ + US(X)^{1/2}) with U independent of X; reason: equivalent to the conditional statement, without conditional laws
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma B.2, p.34; consequence (13), p.35

import Mathlib
import Definitions.Def_PrivGaussMS_Frames

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace PrivGaussMS

/-- **Lemma B.2** (Exact conditional resampling), Moayedi, Yassaee, Ebrahimi, *Optimal Private
Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…), p.34, with its
consequence (13), p.35.

Let `n > max{m, d}` and `X ∼ P^{⊗n}` for a nonsingular Gaussian `P = N(µ, Σ)`. Conditional on
`(X̄, S(X))`, `X =d 1_n X̄ᵀ + U S(X)^{1/2}` with `U` a uniform centered frame independent of the
statistics; consequently a fresh `U` and the first `m` rows give `P^{⊗m}` after averaging over `X`.

**Formalization Note.** The conditional statement is stated without conditional laws: the joint
law of `(X̄, S(X), X)` equals the joint law of `(X̄, S(X), 1_n X̄ᵀ + U S(X)^{1/2})` with `U`
independent of `X`. Row `i` of `1_n x̄ᵀ + U S^{1/2}` is the vector `x̄ + S^{1/2} U_i`. -/
theorem lemma_B_2 {n m d : ℕ} (hm : m < n) (hd : d < n) (μ : Vec d)
    (Sig : Matrix (Fin d) (Fin d) ℝ) (hSig : Sig.PosDef) :
    let P : Measure (Vec d) := multivariateGaussian μ Sig
    let rs : (Fin n → Vec d) → Matrix (Fin n) (Fin d) ℝ → Fin n → Vec d :=
      fun X U i => WithLp.toLp 2 (WithLp.ofLp (mean X) + CFC.sqrt (scatter X) *ᵥ U i)
    (Measure.pi fun _ : Fin n => P).map (fun X => (mean X, scatter X, X)) =
        ((Measure.pi fun _ : Fin n => P).prod (uniformCenteredFrame n d)).map
          (fun q => (mean q.1, scatter q.1, rs q.1 q.2)) ∧
    ((Measure.pi fun _ : Fin n => P).prod (uniformCenteredFrame n d)).map
        (fun q => fun i : Fin m => rs q.1 q.2 (Fin.castLE hm.le i)) =
      Measure.pi fun _ : Fin m => P := by sorry

end PrivGaussMS
