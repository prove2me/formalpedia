-- Prove2me | Theorems.Thm_TaoFivePrimes_montgomery_uncertainty
-- name    : TaoFivePrimes.montgomery_uncertainty
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T00:49:21.300179+00:00
-- url     : https://prove2.me/theorems/7d5d875a-4bfa-4943-bdcd-13a216ac12a2
-- title:
--   Tao Lemma 4.4: Montgomery's uncertainty principle
-- statement:
--   For a cutoff $\eta$, a modulus $q$, a scale $x$ and a frequency $\alpha$, write
--
--   $$S_{\eta,q}(x,\alpha)\;=\;\sum_{n}\Lambda(n)\,e(\alpha n)\,\mathbf 1_{(n,q)=1}\,\eta\!\left(\frac nx\right),$$
--
--   where $\Lambda$ is the von Mangoldt function and $e(t)=e^{2\pi i t}$. Let $q_0\ge1$ divide $q$, let $x\ge1$, and let $\eta$ vanish on $(1,\infty)$. Then
--
--   $$\sum_{\substack{a\bmod q_0\\ (a,q_0)=1}}\Bigl|S_{\eta,q}\Bigl(x,\alpha+\frac a{q_0}\Bigr)\Bigr|^{2}
--   \;\ge\;\frac{\mu(q_0)^{2}}{\varphi(q_0)}\,\bigl|S_{\eta,q}(x,\alpha)\bigr|^{2},$$
--
--   where $\mu$ is the Möbius function and $\varphi$ Euler's totient. For $q_0$ not squarefree the right-hand side vanishes and the inequality is trivial; the content is the squarefree case, where $\mu(q_0)^2=1$.
--
--   This is Montgomery's uncertainty principle: the mass of a prime-supported exponential sum cannot concentrate at a single frequency, since shifting by the $\varphi(q_0)$ reduced fractions $a/q_0$ must recover a definite proportion of it. It is what drives the local $L^2$ estimate (Lemma 4.6) and hence Corollary 4.7, the upper bound on the major-arc $L^2$ mass. Its degenerate case $q_0=2$ is the anti-symmetry $S_{\eta,q}(x,\alpha+\tfrac12)=-S_{\eta,q}(x,\alpha)$ of equation (4.6), and the case of a prime $q_0=p$ reads $\sum_{a=1}^{p-1}|S_{\eta,q}(x,\alpha+a/p)|^{2}\ge|S_{\eta,q}(x,\alpha)|^{2}/(p-1)$.
--
--   **Formalization Note** The residues $a$ modulo $q_0$ are represented by the integers $0\le a<q_0$ coprime to $q_0$. The Möbius function takes integer values, and its square is cast to a real number; the quotient by $\varphi(q_0)$ is the real division, which is harmless since $\varphi(q_0)>0$ for $q_0\ge1$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, Lemma 4.4 (Montgomery's uncertainty principle); originally H. L. Montgomery, A note on the large sieve, J. London Math. Soc. 43 (1968), 93-98

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open Finset

theorem TaoFivePrimes.montgomery_uncertainty
    (eta : ℝ → ℝ) (q q₀ : ℕ) (hq₀ : 0 < q₀) (hdvd : q₀ ∣ q)
    (x alpha : ℝ) (hx : 1 ≤ x) (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ((ArithmeticFunction.moebius q₀ : ℝ) ^ 2 / (Nat.totient q₀ : ℝ))
        * ‖TaoFivePrimes.smoothedExpSum eta q x alpha‖ ^ 2
      ≤ ∑ a ∈ (Finset.range q₀).filter (fun a => Nat.Coprime a q₀),
          ‖TaoFivePrimes.smoothedExpSum eta q x (alpha + (a : ℝ) / q₀)‖ ^ 2 := by sorry
