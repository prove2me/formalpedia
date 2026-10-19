-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_shor_good_probability_totient
-- name    : QAlgorithms.DeWolf.shor_good_probability_totient
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T11:56:44.984095+00:00
-- url     : https://prove2.me/theorems/e1d46891-1344-405b-a723-73a515def0bb
-- title:
--   Shor period finding: success probability proportional to φ(r)/r
-- statement:
--   Let $f:\mathbb N\to\{0,\ldots,N-1\}$ have exact period $r$, meaning that $f(u)=f(v)$ if and only if $u\equiv v\pmod r$, where $1\le r\le N$. Put $\ell=\lceil\log_2(N^2+1)\rceil$ and $q=2^\ell$. Apply the circuit of Figure 5.1 to the zero state: the $q$-point Fourier transform on the first register, the XOR oracle for $f$, and the same Fourier transform again. Measure the first register and let $b$ be its integer value.
--
--   There are absolute constants $a>0$ and $N_0\in\mathbb N$, independent of $N,r,f$, such that for every $N\ge N_0$,
--
--   $$
--   \Pr\left[\exists c\in\{0,\ldots,r-1\}:\ \gcd(c,r)=1\ \text{and}\ \left|\frac bq-\frac cr\right|\le\frac1{2q}\right]\ \ge\ a\,\frac{\varphi(r)}r.
--   $$
--
--   Here $\varphi$ is Euler's totient function, with $\varphi(1)=1$. This is the quantum probability estimate in the period-finding argument, before using the separate number-theoretic estimate for $\varphi(r)/r$. It is uniform over arbitrary bounded functions of exact period $r$, and does not assume that $r$ divides $q$.
--
--   **Formalization Note** The final state is the existing `shorRunState N f`; `probEvent` sums squared amplitudes over the good outcomes of the full two-register state. Omitting the intermediate measurement of the second register preserves the distribution of the first register. The theorem claims an unspecified positive absolute constant, rather than the source's specific $4/\pi^2$ probability for proximity to an unrestricted residue.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, §5.3, Eq. (5.1) and the easy/hard case discussion, printed pp.39–41 (PDF pp.51–53), https://arxiv.org/pdf/1907.09415v6 . This isolates the Fourier probability estimate before the asymptotic estimate for φ(r)/r.

import Definitions.Def_QAlgorithms_Defs_Fourier
import Mathlib.Data.Nat.Totient
set_option autoImplicit false

namespace QAlgorithms.DeWolf

/-- The quantum probability estimate before applying the asymptotic lower bound on φ(r)/r. -/
theorem shor_good_probability_totient :
    ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ, 1 ≤ r → r ≤ N →
      ∀ f : ℕ → ℕ, (∀ t, f t < N) → HasPeriod f r →
        a * ((Nat.totient r : ℝ) / r) ≤ probEvent (shorRunState N f) (fun z =>
          ∃ c : ℕ, c < r ∧ Nat.Coprime c r ∧
            |(bitsToNat z.1 : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤
              1 / (2 * (2 : ℝ) ^ shorEll N)) := by sorry

end QAlgorithms.DeWolf
