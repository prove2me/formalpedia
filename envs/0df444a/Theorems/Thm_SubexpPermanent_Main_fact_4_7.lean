-- Prove2me | Theorems.Thm_SubexpPermanent_Main_fact_4_7
-- name    : SubexpPermanent.Main.fact_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:01:22.712202+00:00
-- url     : https://prove2.me/theorems/6fdb09c5-10c7-4604-bc4c-fc0245856eba
-- title:
--   Fact 4.7 — after $\psi(q)=\log((2-q)/q)$ the matching recursion contracts by $\rho=1-1/s$; $\operatorname{diam}\psi(I)=\log(1+2\gamma)\le s$ and $|d\log q/d\psi|=(2-q)/2\le1$
-- statement:
--   Let $\gamma\ge1$, $I=[1/(1+\gamma),1]$, $\psi(q)=\log\frac{2-q}{q}$ on $I$, $s=\lceil\sqrt{1+4\gamma}\rceil$ and $\rho=1-1/s$. Let $r\ge1$ be an integer and $w_1,\dots,w_r\ge0$ with $\sum_i w_i\le\gamma$. The map $f(x)=(1+\sum_{i=1}^r w_ix_i)^{-1}$ sends $I^r$ to $I$, and for all $x,x'\in I^r$
--   $$|\psi(f(x))-\psi(f(x'))|\le\rho\max_{1\le i\le r}|\psi(x_i)-\psi(x_i')|.$$
--   Moreover, for $q\in I$,
--   $$\operatorname{diam}\psi(I)=\log(1+2\gamma)\le s,\qquad\Big|\frac{d\log q}{d\psi}\Big|=\frac{2-q}{2}\le1\qquad(16).$$
--   The contraction bounds the recursion depth the counting algorithm of Lemma 7.2 needs. The derivative bound turns errors in $\psi$-coordinates into errors in $\log q$.
--
--   **Formalization Note.** The inverse of $\psi$ is $t\mapsto 2/(1+e^t)$. The derivative $d\log q/d\psi$ is stated as the derivative of $t\mapsto\log(2/(1+e^t))$ at $t=\psi(q)$, which equals $-(2-q)/2$, together with the identity $2/(1+e^{\psi(q)})=q$.
--
--   Differences from the source:
--
--   - encoding: f : I^r → I (part of the definition of f) → an explicit first clause: f(x) ∈ I for every x ∈ I^r; reason: states the claim implicit in the definition
--   - encoding: max over 1 ≤ i ≤ r → ⨆ over i : Fin r (a finite nonempty index set since r ≥ 1); reason: a supremum of finitely many reals is their maximum
--   - encoding: |d log q / dψ| = (2 − q)/2 → HasDerivAt (t ↦ log(2/(1 + e^t))) (−(2 − q)/2) at ψ(q), with 2/(1 + e^{ψ(q)}) = q and |−(2 − q)/2| = (2 − q)/2; reason: t ↦ 2/(1 + e^t) is the inverse of ψ, so this is the derivative of log q as a function of ψ
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 15, Fact 4.7, eq. (16)

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Contraction

namespace SubexpPermanent.Main

/-- Fact 4.7 (contraction of the matching recursion), p. 15. The derivative `d log q / dψ` is
the derivative of `t ↦ log ψ⁻¹(t)` at `t = ψ(q)`, where `ψ⁻¹(t) = 2/(1 + e^t)`. -/
theorem fact_4_7 (γ : ℝ) (hγ : 1 ≤ γ) (r : ℕ) (hr : 1 ≤ r) (w : Fin r → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwγ : ∑ i, w i ≤ γ) :
    (∀ x : Fin r → ℝ, (∀ i, x i ∈ unmatchedInterval γ) →
      (1 + ∑ i, w i * x i)⁻¹ ∈ unmatchedInterval γ) ∧
    (∀ x x' : Fin r → ℝ, (∀ i, x i ∈ unmatchedInterval γ) → (∀ i, x' i ∈ unmatchedInterval γ) →
      |psi (1 + ∑ i, w i * x i)⁻¹ - psi (1 + ∑ i, w i * x' i)⁻¹| ≤
        rhoContr γ * ⨆ i, |psi (x i) - psi (x' i)|) ∧
    Metric.diam (psi '' unmatchedInterval γ) = Real.log (1 + 2 * γ) ∧
    Real.log (1 + 2 * γ) ≤ (sCeil γ : ℝ) ∧
    ∀ q ∈ unmatchedInterval γ,
      2 / (1 + Real.exp (psi q)) = q ∧
      HasDerivAt (fun t => Real.log (2 / (1 + Real.exp t))) (-(2 - q) / 2) (psi q) ∧
      |(-(2 - q) / 2)| = (2 - q) / 2 ∧ (2 - q) / 2 ≤ 1 := by sorry

end SubexpPermanent.Main
