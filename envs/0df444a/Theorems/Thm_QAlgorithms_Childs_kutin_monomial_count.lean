-- Prove2me | Theorems.Thm_QAlgorithms_Childs_kutin_monomial_count
-- name    : QAlgorithms.Childs.kutin_monomial_count
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T21:18:17.033644+00:00
-- url     : https://prove2.me/theorems/77e33b95-700e-4cba-a1a2-d704ef0e9d18
-- title:
--   Kutin's exact permutation average for a consistent indicator monomial
-- statement:
--   Fix a valid collision triple $(m,a,b)$ for a domain and alphabet of size $n$: $0\le m\le n$, $a,b\ge1$, $a\mid m$, and $b\mid n-m$. Let $E\subseteq[n]\times[n]$ be a finite set of input-output constraints, with at most one required output for each input. Write $J$ for its set of output labels, $s=|E|$, $t=|J|$, and $c_j=|\{i:(i,j)\in E\}|$.
--
--   For independent uniform permutations $\sigma,\tau$ of $[n]$, let $\delta^{\sigma\tau}_{ij}$ indicate that $\tau(x^{m,a,b}_{\sigma(i)})=j$, where $x^{m,a,b}$ is the specified $a$-to-one/$b$-to-one collision input. With the real falling factorial $(z)_r=\prod_{q=0}^{r-1}(z-q)$, the exact average is
--
--   $$
--   \mathbb E_{\sigma,\tau}\prod_{(i,j)\in E}\delta^{\sigma\tau}_{ij}
--   =\frac{1}{(n)_s(n)_t}\sum_{U\subseteq J}
--   \left(\frac ma\right)_{|U|}
--   \left(\frac{n-m}{b}\right)_{|J\setminus U|}
--   \prod_{j\in U}(a)_{c_j}\prod_{j\in J\setminus U}(b)_{c_j}.
--   $$
--
--   Empty products are one. Consistency implies $s,t\le n$, so both denominator factors are positive, including the empty case $n=0$. This is the explicit counting identity used by Kutin's symmetrization lemma; it isolates the combinatorics from the subsequent cancellation and polynomial degree argument.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, printed pp.105–106 (PDF pp.113–114), proof of Lemma 22.1, equations (22.8)–(22.16). https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Polynomial
set_option autoImplicit false

namespace QAlgorithms.Childs

theorem kutin_monomial_count (n m a b : ℕ) (h : ValidKutinTriple n m a b)
    (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, ∀ f ∈ E, e.1 = f.1 → e.2 = f.2) :
    let J := E.image Prod.snd
    let c := fun j => (E.filter (fun e => e.2 = j)).card
    (((n.factorial : ℝ) ^ 2)⁻¹ *
      ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        ∏ e ∈ E, kutinDelta n m a b σ τ e) =
    ((n.descFactorial E.card : ℝ) * (n.descFactorial J.card : ℝ))⁻¹ *
      ∑ U ∈ J.powerset,
        (∏ q ∈ Finset.range U.card, ((m : ℝ) / a - q)) *
        (∏ q ∈ Finset.range (J \ U).card, (((n : ℝ) - m) / b - q)) *
        (∏ j ∈ U, ∏ q ∈ Finset.range (c j), ((a : ℝ) - q)) *
        (∏ j ∈ J \ U, ∏ q ∈ Finset.range (c j), ((b : ℝ) - q)) := by sorry

end QAlgorithms.Childs
