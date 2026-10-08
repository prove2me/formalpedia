-- Prove2me | Theorems.Thm_UnivESD_Universality_lemma_3_3
-- name    : UnivESD.Universality.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:39.729986+00:00
-- url     : https://prove2.me/theorems/c1fb48a0-6a40-42c7-a3de-9f31dd5f880b
-- title:
--   Lemma 3.3 (Girko's identity): $m(u,v)=\frac{u^2+v^2}{4\pi iu}\int_{\mathbb R}\int_{\mathbb R}g(s+it)e^{ius+ivt}\,dt\,ds$
-- statement:
--   Let $A$ be an $n\times n$ complex matrix and $\mu=\mu_{\frac1{\sqrt n}A}$ the ESD of $\frac1{\sqrt n}A$, with eigenvalues $\lambda_j$ of $A$. Let
--   $$m(u,v)=\int_{\mathbb C}e^{iu\,\mathrm{Re}(z)+iv\,\mathrm{Im}(z)}\,d\mu(z),\qquad g(z)=2\,\mathrm{Re}\int_{\mathbb C}\frac{z-w}{|z-w|^2}\,d\mu(w)=\frac2n\,\mathrm{Re}\sum_{j=1}^n\frac{z-\lambda_j/\sqrt n}{|z-\lambda_j/\sqrt n|^2}.$$
--   Then for all nonzero real $u,v$,
--   $$m(u,v)=\frac{u^2+v^2}{4\pi iu}\int_{\mathbb R}\Bigl(\int_{\mathbb R}g(s+it)\,e^{ius+ivt}\,dt\Bigr)ds,$$
--   where the inner integral is absolutely integrable for almost every $s$ and the outer integral is absolutely convergent.
--
--   Girko's identity expresses the characteristic function of the ESD through the transform $g$, which is the $\mathrm{Re}(z)$-derivative of $\frac2n\log|\det(\frac1{\sqrt n}A-zI)|$; it is the bridge from log-determinants to ESDs.
--
--   **Formalization Note.** The identity is deterministic and stated for every $n$ and every matrix $A$. At an atom ($z=\lambda_j/\sqrt n$) Lean's convention $x/0=0$ sets the integrand of $g$ to $0$; this concerns finitely many points and does not affect any integral. The three conclusions are: integrability of the inner integrand for a.e. $s$, integrability of the outer integrand, and the identity.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2039 (PDF 17), Lemma 3.3, with m from p. 2038 (PDF 16) and g from (3.6), p. 2039

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Lemma 3.3 (Girko's identity), p. 2039. -/
theorem lemma_3_3 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    (∀ᵐ s : ℝ, Integrable fun t : ℝ =>
        (stieltjesG (esd (invSqrt n • A)) ⟨s, t⟩ : ℂ) *
          Complex.exp (Complex.I * ((u : ℂ) * s + (v : ℂ) * t))) ∧
      Integrable (fun s : ℝ => ∫ t : ℝ,
        (stieltjesG (esd (invSqrt n • A)) ⟨s, t⟩ : ℂ) *
          Complex.exp (Complex.I * ((u : ℂ) * s + (v : ℂ) * t))) ∧
      charFn (esd (invSqrt n • A)) u v =
        ((u : ℂ) ^ 2 + (v : ℂ) ^ 2) / (4 * (Real.pi : ℂ) * Complex.I * u) *
          ∫ s : ℝ, ∫ t : ℝ, (stieltjesG (esd (invSqrt n • A)) ⟨s, t⟩ : ℂ) *
            Complex.exp (Complex.I * ((u : ℂ) * s + (v : ℂ) * t)) := by sorry

end UnivESD.Universality
