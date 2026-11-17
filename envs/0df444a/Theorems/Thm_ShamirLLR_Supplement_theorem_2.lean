-- Prove2me | Theorems.Thm_ShamirLLR_Supplement_theorem_2
-- name    : ShamirLLR.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:24:39.20222+00:00
-- url     : https://prove2.me/theorems/f984fe7b-d68d-44a4-8b4e-ba6e959574d2
-- title:
--   Theorem 2 — arbitrary positive relative degrees: for $1/\ell<c<1/2$ and $\log p\ge Cm^{\Theta_\ell}\log(2m)$, $\mathbb E_a\,\mathrm{Insec}\le2(2/\pi)^{(1-\varepsilon)d}$
-- statement:
--   Let $\tau=2/\pi$ and let $\mathbb E_a$ denote the uniform average over $\mathcal A_{p,m}$, the ordered $m$-tuples of distinct nonzero places of $\mathbb F_p$; $\Delta(a;r)$ is the Reed–Solomon codeword-versus-independent-input distance (1) and $\mathrm{Insec}(a;d)$ the one-bit local-leakage insecurity of Shamir sharing.
--
--   For every fixed integer $\ell\ge4$ there is a finite exponent $\Theta_\ell>0$ with the following three properties.
--
--   1. Fix $1/\ell<c<1/2$ and $0<\varepsilon<1$, and put $d=\lfloor cm\rfloor$. There are constants $C_{c,\ell,\varepsilon},m_{c,\ell,\varepsilon}>0$ such that for every $m\ge m_{c,\ell,\varepsilon}$ and every prime $p$ with $\log p\ge C_{c,\ell,\varepsilon}\,m^{\Theta_\ell}\log(2m)$,
--   $$
--   \mathbb E_a\,\Delta(a;d)\le\tau^{(1-\varepsilon)d},\qquad \mathbb E_a\,\mathrm{Insec}(a;d)\le2\,\tau^{(1-\varepsilon)d}. \tag{5}
--   $$
--   2. If $m\to\infty$ and $\log p/(m^{\Theta_\ell}\log(2m))\to\infty$, both quantities are at most $\tau^{(1-o(1))d}$.
--   3. For $n$-bit primes $2^{n-1}<p<2^n$ this holds uniformly with $m=\lfloor n^u\rfloor$ and any fixed $0<u<1/\Theta_\ell$.
--
--   The theorem extends Theorem 1 from relative degrees $c>1/3$ to every fixed $0<c<1/2$, keeping the optimal base $2/\pi$ at the price of a larger field. The exponent $\Theta_\ell$ is existential; Eq. (77) of the paper gives a permissible value in terms of an unspecified exponent of Leng, and the statement does not fix it.
--
--   **Formalization Note.** One $\Theta_\ell$ serves all three clauses. The two asymptotic clauses carry no factor $2$ on the $\mathrm{Insec}$ bound, as printed.
--
--   Differences from the source:
--   - reading: "both quantities are at most $(2/\pi)^{(1-o(1))d}$" when $m\to\infty$ and $\log p/(m^{\Theta_\ell}\log(2m))\to\infty$ → for every $1/\ell<c<1/2$ and every sequence $(m_j,p_j)$ with $p_j$ prime, $m_j\to\infty$ and $\log p_j/(m_j^{\Theta_\ell}\log(2m_j))\to\infty$, some $o_j\to0$ with both bounds for all large $j$; reason: the asymptotic statement along every admissible sequence, as in the published goal's general clause
--   - reading: "For $n$-bit primes, this holds uniformly with $m=\lfloor n^u\rfloor$ and any fixed $0<u<1/\Theta_\ell$" → for every $1/\ell<c<1/2$ and $0<u<1/\Theta_\ell$, a function $o:\mathbb N\to\mathbb R$ with $o(n)\to0$, chosen before $n$ and $p$, with both bounds for all large $n$ and every prime $2^{n-1}<p<2^n$; reason: the printed quantifier order (uniformly over the primes), as in the published goal's Eq. (4)
--   - encoding: $\mathbb E_a$ over uniform ordered distinct nonzero tuples → the Finset average `avgTuples p m` over $\mathcal A_{p,m}$ (published `ShamirLLR.evalTuples`); reason: it is $0$ only on an empty $\mathcal A_{p,m}$, which the field-size hypotheses exclude for large $m$ and $n$
--   - encoding: $d=\lfloor cm\rfloor$, $m=\lfloor n^u\rfloor$, $m^{\Theta_\ell}$, $(2/\pi)^{(1-\varepsilon)d}$, $\log$ → natural floors, real powers, natural logarithm; reason: Lean conventions; $\log$ is natural (p.13)
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Theorem 2, Eq. (5), p.3 (PDF p.4); proof §10, pp.66–91 (PDF pp.67–92); bit length $n$, p.2

import Mathlib
import Definitions.Def_ShamirLLR_evalTuples
import Definitions.Def_ShamirLLR_deltaClass
import Definitions.Def_ShamirLLR_insec

set_option autoImplicit false

open Filter Topology

namespace ShamirLLR.Supplement

/-- **Theorem 2 (Arbitrary positive relative degrees).** For every fixed integer `ℓ ≥ 4` there is
a finite exponent `Θ_ℓ > 0` with the following property.
1. Fix `1/ℓ < c < 1/2` and `0 < ε < 1`, and put `d = ⌊cm⌋`. There are constants
   `C_{c,ℓ,ε}, m_{c,ℓ,ε} > 0` such that for every `m ≥ m_{c,ℓ,ε}` and every prime `p` with
   `log p ≥ C_{c,ℓ,ε} m^{Θ_ℓ} log(2m)`, `𝔼_a Δ(a; d) ≤ (2/π)^{(1−ε)d}` and
   `𝔼_a Insec(a; d) ≤ 2 (2/π)^{(1−ε)d}` (5).
2. If `m → ∞` and `log p / (m^{Θ_ℓ} log(2m)) → ∞`, both quantities are at most
   `(2/π)^{(1−o(1))d}`.
3. For `n`-bit primes this holds uniformly with `m = ⌊n^u⌋` and any fixed
   `0 < u < u₀(ℓ) = 1/Θ_ℓ`.

Here `𝔼_a` is the uniform average over `A_{p,m}` (ordered tuples of distinct nonzero places).

Source: Hwang–Maji–Shkredov–Ye, *Local Leakage Resilience of Multiplication-friendly Shamir
Secret Sharing*, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…), Theorem 2, Eq. (5),
p.3; proof in §10, pp.66–91; `n` the bit length of `p`, p.2.

**Formalization Note.** One `Θ_ℓ` is chosen after `ℓ` and serves all three clauses; it is not
pinned to the permissible value of Eq. (77). `p` is prime as printed ("every prime p"); `d = ⌊cm⌋`
and `m = ⌊n^u⌋` are natural floors; `m^{Θ_ℓ}` and the exponents are real powers; `log` is natural.
Each `o(1)` is a function `o : ℕ → ℝ` tending to `0`, chosen after `c` (and `u`) and before `n`
(resp. after the sequence), and the bounds hold for all large `n` and every prime in
`(2^{n−1}, 2^n)` (resp. for all large `j`), as in the published `ShamirLLR.theorem_1`. As printed,
the asymptotic clauses carry no factor `2` on the `Insec` bound. -/
theorem theorem_2 :
    ∀ ℓ : ℕ, 4 ≤ ℓ → ∃ Θ : ℝ, 0 < Θ ∧
      (∀ c ε : ℝ, 1 / (ℓ : ℝ) < c → c < 1 / 2 → 0 < ε → ε < 1 →
        ∃ C m₀ : ℝ, 0 < C ∧ 0 < m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∀ (p : ℕ) [Fact p.Prime],
          C * (m : ℝ) ^ Θ * Real.log (2 * m) ≤ Real.log p →
            avgTuples p m (fun a => delta a ⌊c * m⌋₊) ≤
                (2 / Real.pi) ^ ((1 - ε) * (⌊c * m⌋₊ : ℝ)) ∧
              avgTuples p m (fun a => insec a ⌊c * m⌋₊) ≤
                2 * (2 / Real.pi) ^ ((1 - ε) * (⌊c * m⌋₊ : ℝ))) ∧
      (∀ c : ℝ, 1 / (ℓ : ℝ) < c → c < 1 / 2 → ∀ (m p : ℕ → ℕ) [∀ j, Fact (p j).Prime],
        Tendsto m atTop atTop →
        Tendsto (fun j => Real.log (p j) / ((m j : ℝ) ^ Θ * Real.log (2 * m j))) atTop atTop →
        ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧ ∀ᶠ j : ℕ in atTop,
          avgTuples (p j) (m j) (fun a => delta a ⌊c * m j⌋₊) ≤
              (2 / Real.pi) ^ ((1 - o j) * (⌊c * m j⌋₊ : ℝ)) ∧
            avgTuples (p j) (m j) (fun a => insec a ⌊c * m j⌋₊) ≤
              (2 / Real.pi) ^ ((1 - o j) * (⌊c * m j⌋₊ : ℝ))) ∧
      (∀ c u : ℝ, 1 / (ℓ : ℝ) < c → c < 1 / 2 → 0 < u → u < 1 / Θ →
        ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
          ∀ (p : ℕ) [Fact p.Prime], 2 ^ (n - 1) < p → p < 2 ^ n →
            avgTuples p ⌊(n : ℝ) ^ u⌋₊ (fun a => delta a ⌊c * ⌊(n : ℝ) ^ u⌋₊⌋₊) ≤
                (2 / Real.pi) ^ ((1 - o n) * (⌊c * ⌊(n : ℝ) ^ u⌋₊⌋₊ : ℝ)) ∧
              avgTuples p ⌊(n : ℝ) ^ u⌋₊ (fun a => insec a ⌊c * ⌊(n : ℝ) ^ u⌋₊⌋₊) ≤
                (2 / Real.pi) ^ ((1 - o n) * (⌊c * ⌊(n : ℝ) ^ u⌋₊⌋₊ : ℝ))) := by sorry

end ShamirLLR.Supplement
