-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_shor_periodFinding
-- name    : QAlgorithms.DeWolf.shor_periodFinding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:34:57.788865+00:00
-- url     : https://prove2.me/theorems/d1f72f49-9a9d-41a5-92de-560783bd030b
-- title:
--   One run of Shor's period-finding circuit reveals the period with probability Omega(1/log log N)
-- statement:
--   The period-finding problem: we are given $f:\mathbb N\to\{0,\dots,N-1\}$ for which there is an unknown $r\in\{1,\dots,N\}$ with $f(a)=f(b)$ if and only if $a\equiv b\pmod r$.
--
--   Let $q=2^\ell$ be the power of two with $N^2<q\le2N^2$ and $n=\lceil\log_2N\rceil$. Let $O_f$ be the unitary $|a\rangle|z\rangle\mapsto|a\rangle|z\oplus f(a)\rangle$ on $\ell+n$ qubits, with $a$ read as an $\ell$-bit number and $f(a)$ written in $n$ bits, and let $F_q$ be the quantum Fourier transform on the first register. One run of Shor's algorithm prepares
--
--   $$
--   |\Phi\rangle=(F_q\otimes I)\,O_f\,(F_q\otimes I)\,|0^\ell\rangle|0^n\rangle
--   $$
--
--   (one evaluation of $f$ and two Fourier transforms) and measures the first register in the computational basis, obtaining $b\in\{0,\dots,q-1\}$. Call $b$ good if
--
--   $$
--   \Big|\frac bq-\frac cr\Big|\le\frac1{2q}\quad\text{for some } c\in\{0,\dots,r-1\} \text{ with } \gcd(c,r)=1 .
--   $$
--
--   Then:
--
--   1. There are constants $C>0$ and $N_0$ such that for every $N\ge N_0$, every $r\in\{1,\dots,N\}$ and every $f$ as above with period $r$, the outcome is good with probability at least $C/\log\log N$. Hence an expected number of $O(\log\log N)$ independent runs (each with one evaluation of $f$ and two QFTs) produces a good outcome.
--   2. If $|b/q-c/r|\le1/(2q)$ with $1\le r\le N$, $0\le c<r$ and $\gcd(c,r)=1$, then $c/r$ is the only fraction $p/s$ with $1\le s\le N$ within distance $1/(2q)$ of $b/q$, and the denominator of $c/r$ in lowest terms is $r$.
--
--   So a good outcome determines $r$: continued-fraction expansion of $b/q$ finds the unique fraction with denominator at most $N$ near $b/q$, and its denominator is the period. This is the quantum core of Shor's factoring algorithm.
--
--   **Formalization Note** The state $|\Phi\rangle$ is the shared `shorRunState`, with $\ell=\lceil\log_2(N^2+1)\rceil$ (which gives $N^2<2^\ell\le2N^2$) and second register $\lceil\log_2N\rceil$ qubits. The intermediate measurement of the second register is omitted: it does not change the distribution of the first register. The probability of a good outcome is the total weight of the basis states whose first register is good. The constants $C$ and $N_0$ are quantified before $N$, $r$ and $f$. The source's per-run constant $4/\pi^2$ is not stated (see notes).
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 51, §5.3. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Fourier
set_option autoImplicit false

namespace QAlgorithms.DeWolf


open Classical in
/-- de Wolf §5.3, PDF pp.50–53 (unnumbered): Shor's period-finding algorithm. Let
`f : ℕ → {0, …, N − 1}` have period `r ∈ {1, …, N}` (`f(a) = f(b)` iff `a ≡ b mod r`, p.50), let
`q = 2^ℓ` with `N² < q ≤ 2N²` (`ℓ = shorEll N`), and run the circuit of Figure 5.1 once:
`F_q` on the first (`ℓ`-qubit) register of `|0^ℓ⟩|0^n⟩` (`n = ⌈log N⌉`), one application of
`O_f : |a⟩|z⟩ ↦ |a⟩|z ⊕ f(a)⟩`, `F_q` on the first register, and measure the first register,
obtaining `b`. Then:

1. there are constants `C > 0` and `N₀`, independent of `N`, `r`, `f`, such that for all `N ≥ N₀`
   the outcome `b` satisfies `|b/q − c/r| ≤ 1/(2q)` for some `c ∈ {0, …, r − 1}` coprime to `r`
   with probability at least `C / log log N` (so `O(log log N)` expected repetitions suffice);
2. whenever `|b/q − c/r| ≤ 1/(2q)` with `c` coprime to `r ≤ N`, the fraction `c/r` is the only
   fraction with denominator `≤ N` within `1/(2q)` of `b/q`, and its lowest-terms denominator
   is `r`. -/
theorem shor_periodFinding :
    (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ, 1 ≤ r → r ≤ N →
      ∀ f : ℕ → ℕ, (∀ a, f a < N) → HasPeriod f r →
        C / Real.log (Real.log N) ≤ probEvent (shorRunState N f) fun z =>
          ∃ c : ℕ, c < r ∧ Nat.Coprime c r ∧
            |(bitsToNat z.1 : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤
              1 / (2 * (2 : ℝ) ^ shorEll N)) ∧
    (∀ N r c b : ℕ, 1 ≤ r → r ≤ N → c < r → Nat.Coprime c r →
      |(b : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤ 1 / (2 * (2 : ℝ) ^ shorEll N) →
        ((c : ℚ) / r).den = r ∧
        ∀ (p : ℤ) (s : ℕ), 1 ≤ s → s ≤ N →
          |(b : ℝ) / (2 : ℝ) ^ shorEll N - (p : ℝ) / s| ≤ 1 / (2 * (2 : ℝ) ^ shorEll N) →
            (p : ℝ) / s = (c : ℝ) / r) := by
  sorry

end QAlgorithms.DeWolf
