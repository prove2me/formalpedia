-- Prove2me | Theorems.Thm_RamanujanPetersson_trace_heckeT_mul_diamond_gamma1
-- name    : RamanujanPetersson.trace_heckeT_mul_diamond_gamma1
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:58:15.069048+00:00
-- url     : https://prove2.me/theorems/822ca8a9-0b3f-4e9a-b118-92f785f07d8a
-- title:
--   Eichler-Selberg trace formula for $T_n\langle\delta\rangle$ on $S_k(\Gamma_1(M))$, $k\ge3$, $M\ge3$
-- statement:
--   Let $M\ge3$, $k\ge3$ and $n\ge1$ be integers with $\gcd(n,M)=1$, and let $\delta\in(\mathbb Z/M\mathbb Z)^\times$. For $f\in S_k(\Gamma_1(M))$ write $f=\sum_{m\ge0}a_m(f)q^m$, $q=e^{2\pi i z}$, and for $d$ prime to $M$ let $\langle d\rangle f=f|_k\gamma$ for any $\gamma=\begin{pmatrix}a&b\\c&d'\end{pmatrix}\in\Gamma_0(M)$ with $d'\equiv d\pmod M$ (the diamond operator). Then there is a unique $\mathbb C$-linear map $T=T_n\langle\delta\rangle$ of $S_k(\Gamma_1(M))$ with
--
--   $$a_m(Tf)=\sum_{d\mid\gcd(m,n)}d^{k-1}\,a_{mn/d^2}\big(\langle d\delta\rangle f\big)\qquad(m\ge0),$$
--
--   and its trace is given by the Eichler-Selberg trace formula
--
--   $$\operatorname{Tr}\big(T_n\langle\delta\rangle\mid S_k(\Gamma_1(M))\big)=A_1+A_2+A_3,$$
--
--   where:
--
--   - (scalar term) $A_1=0$ unless $n=s^2$ is a square, in which case $A_1=\frac{k-1}{12}\,\psi(M)\,s^{k-2}\,\frac{\varphi(M)}{2}\big([\delta s\equiv1]+(-1)^k[\delta s\equiv-1]\big)$, congruences mod $M$, $\psi(M)=M\prod_{\ell\mid M}(1+1/\ell)$;
--   - (elliptic term) $A_2=-\sum_{t\in\mathbb Z,\ t^2<4n}U_{k-2}(t,n)\sum_{Q}\frac{N_Q}{w_Q}$, where $Q=[a,b,c]$ runs over the reduced positive definite integral binary quadratic forms (primitive or not) of discriminant $b^2-4ac=t^2-4n$, i.e. $|b|\le a\le c$ with $b\ge0$ if $|b|=a$ or $a=c$; $w_Q=6$, $4$ or $2$ according as $Q$ is a multiple of $x^2+xy+y^2$, of $x^2+y^2$, or neither; $N_Q$ is the number of $v\in(\mathbb Z/M\mathbb Z)^2$ of exact additive order $M$ with $g_Qv=\delta^{-1}v$ for $g_Q=\begin{pmatrix}(t-b)/2&-c\\a&(t+b)/2\end{pmatrix}$; and $U_{k-2}(t,n)=\frac{\rho^{k-1}-\bar\rho^{k-1}}{\rho-\bar\rho}$ for the roots $\rho,\bar\rho$ of $X^2-tX+n$;
--   - (hyperbolic term) $A_3=-\frac12\sum_{e\mid n}\min(e,n/e)^{k-1}\sum_{\tau\mid M}\frac{\varphi(g_\tau)}{g_\tau}\sum_{x}c_{M/g_\tau}(\delta x)$, where $g_\tau=\gcd(\tau,M/\tau)$, $x$ runs over $0\le x<M$ with $x\equiv e\pmod\tau$ and $x\equiv n/e\pmod{M/\tau}$, and $c_L(z)=\sum_{\chi\bmod L,\ \chi(-1)=(-1)^k}\chi(z)$, that is $c_L(z)=\frac{\varphi(L)}2\big([z\equiv1]+(-1)^k[z\equiv-1]\big)\pmod L$ for $L\ge3$ and $c_L(z)=[k\text{ even}]\,[\gcd(z,L)=1]$ for $L\le2$.
--
--   (The Eisenstein term $A_4$ of the general formula vanishes for $k\ge3$.)
--
--   Role: this is the Eichler-Selberg trace formula, in the explicit form of Cohen and Oesterlé, for the full space of cusp forms on $\Gamma_1(M)$; summing over the nebentypus characters with weights $\chi(\delta)$ recovers the formula on each $S_k(\Gamma_0(M),\chi)$. For $n=1$, $\delta=1$ it gives $\dim S_k(\Gamma_1(M))$. It is the classical tool for computing traces of Hecke operators, and its comparison with point counts of elliptic curves over finite fields is the starting point of the Eichler-Shimura-Ihara-Deligne approach to the Ramanujan-Petersson conjecture.
--
--   **Formalization Note**: $S_k(\Gamma_1(M))$ is Mathlib's `CuspForm` for the image of `CongruenceSubgroup.Gamma1 M` in $GL_2(\mathbb R)$, $a_m(f)$ is `(qExpansion 1 f).coeff m`, and $f|_k\gamma$ is the slash action `⇑f ∣[(k : ℤ)] γ`. The diamond operators enter through an arbitrary family $d\mapsto\gamma_d\in\Gamma_0(M)$ whose lower-right entry is $\equiv d\delta\pmod M$: the characterizing property quantifies over all such families, and the statement asserts that exactly one linear map $T$ has it (`∀ T', P T' ↔ T' = T`), so $T$ exists and is unique. The divisor sum is written over `(Nat.gcd m n).divisors` filtered by `d.Coprime M` (automatic here since $\gcd(n,M)=1$). $U_{k-2}(t,n)$ is the top-left entry of $\begin{pmatrix}t&-n\\1&0\end{pmatrix}^{k-2}$; the reduced forms are enumerated as a filter of the integer box $[0,|D|]\times[-|D|,|D|]\times[0,|D|]$, $D=t^2-4n$; the sum over $t$ runs over $|t|\le2n$ (only $t^2<4n$ contributes, since there are no reduced positive definite forms of discriminant $\ge0$); $c_L$ is written in the closed form above; the trace is `LinearMap.trace ℂ` and the right-hand side is a rational number cast to `ℂ`.
-- source:
--   H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Theorem 12.4.11; H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976

import Mathlib

open UpperHalfPlane MatrixGroups ModularForm

theorem RamanujanPetersson.trace_heckeT_mul_diamond_gamma1 (M : ℕ) [NeZero M] (hM : 3 ≤ M)
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    ∃ T : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
        CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ T' : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
          CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k,
        (∀ γ : ℕ → SL(2, ℤ),
          (∀ d : ℕ, d.Coprime M →
            γ d ∈ CongruenceSubgroup.Gamma0 M ∧ (((γ d) 1 1 : ℤ) : ZMod M) = (d : ZMod M) * (δ : ZMod M)) →
          ∀ (f : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
            (m : ℕ),
            (qExpansion 1 (T' f)).coeff m =
              ∑ d ∈ (Nat.gcd m n).divisors with d.Coprime M,
                (d : ℂ) ^ (k - 1) * (qExpansion 1 (⇑f ∣[(k : ℤ)] γ d)).coeff (m * n / d ^ 2)) ↔
          T' = T) ∧
      LinearMap.trace ℂ _ T =
        (((if Nat.sqrt n * Nat.sqrt n = n then
              ((k : ℚ) - 1) / 12 * ((M : ℚ) * ∏ l ∈ M.primeFactors, (1 + 1 / (l : ℚ))) *
                (Nat.sqrt n : ℚ) ^ (k - 2) * ((Nat.totient M : ℚ) / 2 *
                  ((if (δ : ZMod M) * (Nat.sqrt n : ZMod M) = 1 then 1 else 0) +
                    (-1) ^ k * (if (δ : ZMod M) * (Nat.sqrt n : ZMod M) = -1 then 1 else 0)))
            else 0) -
          (∑ t ∈ Finset.Icc (-(2 * n : ℤ)) (2 * n),
              ((((!![t, -(n : ℤ); 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ (k - 2)) 0 0 : ℤ) : ℚ) *
                (∑ Q ∈ (Finset.Icc (0 : ℤ) (t ^ 2 - 4 * n).natAbs ×ˢ
                      Finset.Icc (-((t ^ 2 - 4 * n).natAbs : ℤ)) (t ^ 2 - 4 * n).natAbs ×ˢ
                      Finset.Icc (0 : ℤ) (t ^ 2 - 4 * n).natAbs).filter
                    (fun Q : ℤ × ℤ × ℤ => 1 ≤ Q.1 ∧ Q.2.1 ^ 2 - 4 * Q.1 * Q.2.2 = t ^ 2 - 4 * n ∧
                      -Q.1 ≤ Q.2.1 ∧ Q.2.1 ≤ Q.1 ∧ Q.1 ≤ Q.2.2 ∧
                      (0 ≤ Q.2.1 ∨ (Q.2.1 ≠ -Q.1 ∧ Q.1 ≠ Q.2.2))),
                  (((Finset.univ.filter fun v : Fin 2 → ZMod M =>
                      addOrderOf v = M ∧
                        ((!![(t - Q.2.1) / 2, -Q.2.2; Q.1, (t + Q.2.1) / 2] : Matrix (Fin 2) (Fin 2) ℤ).map
                          (Int.castRingHom (ZMod M))).mulVec v = ((δ⁻¹ : (ZMod M)ˣ) : ZMod M) • v).card : ℚ) /
                    ((if Q.1 = Q.2.1 ∧ Q.2.1 = Q.2.2 then 6 else if Q.2.1 = 0 ∧ Q.1 = Q.2.2 then 4 else 2 : ℕ) :
                      ℚ)))) -
          1 / 2 * (∑ e ∈ n.divisors, ((min e (n / e) : ℕ) : ℚ) ^ (k - 1) *
            (∑ τ ∈ M.divisors, (Nat.totient (Nat.gcd τ (M / τ)) : ℚ) / (Nat.gcd τ (M / τ) : ℚ) *
              (∑ x ∈ (Finset.range M).filter (fun x : ℕ =>
                  (x : ℤ) ≡ (e : ℤ) [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ ((n / e : ℕ) : ℤ) [ZMOD ((M / τ : ℕ) : ℤ)]),
                (if M / Nat.gcd τ (M / τ) ≤ 2 then
                  (if Even k ∧ Nat.Coprime ((δ : ZMod M).val * x) (M / Nat.gcd τ (M / τ)) then 1 else 0)
                else (Nat.totient (M / Nat.gcd τ (M / τ)) : ℚ) / 2 *
                  ((if (((δ : ZMod M).val * x : ℕ) : ZMod (M / Nat.gcd τ (M / τ))) = 1 then 1 else 0) +
                    (-1) ^ k *
                      (if (((δ : ZMod M).val * x : ℕ) : ZMod (M / Nat.gcd τ (M / τ))) = -1 then 1 else 0))))))
          : ℚ) : ℂ) := by
  sorry
