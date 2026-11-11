-- Prove2me | Theorems.Thm_RSVProductQLTC_ProductExpansion_theorem_5_9
-- name    : RSVProductQLTC.ProductExpansion.theorem_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:29.678235+00:00
-- url     : https://prove2.me/theorems/fe9abba9-cca1-46bc-9b93-244a5eb0818d
-- title:
--   Theorem 5.9 — good binary quantum locally testable CSS codes, assuming Conjecture 5.6
-- statement:
--   Assume Conjecture 5.6 (uniform product expansion of Reed–Solomon codes on the norm-one subgroups of binary extension fields). Then there exist constants $c_K,c_D,\kappa>0$ and $q\in\mathbb N$ such that for every $n_0$ there is a binary CSS code on $N\ge n_0$ qubits, given by check matrices $H_X\in\mathbb F_2^{m_X\times N}$ and $H_Z\in\mathbb F_2^{m_Z\times N}$ with $H_XH_Z^{\mathsf T}=0$, satisfying
--   $$K=N-\operatorname{rank}H_X-\operatorname{rank}H_Z\ \ge\ c_K N,\qquad D\ \ge\ c_D N,$$
--   where $D=\min(d_X,d_Z)$ is the quantum distance ($d_X$ the minimum weight of a vector in $\ker H_Z\setminus\operatorname{row}H_X$, and symmetrically $d_Z$), both codes $\ker H_X$ and $\ker H_Z$ are $\kappa$-locally testable with $q$ queries with respect to the rows of $H_X$ and $H_Z$ (Definitions 1.1–1.2; in particular every check has weight at most $q$), and every column of $H_X$ and of $H_Z$ has weight at most $q$.
--
--   This is the paper's main theorem: an infinite family of good quantum locally testable codes (constant rate, linear distance, constant soundness, constant locality) over a binary alphabet, conditional on Conjecture 5.6.
--
--   **Formalization Note.** "Infinite family" is rendered as: codes of length $N\ge n_0$ for every $n_0$, with all constants chosen before $n_0$ (so they are uniform over the family). $\Omega(N)$ bounds are $c_KN\le K$ and $\lceil c_DN\rceil\le D$ in $\mathbb N\cup\{\infty\}$ (equivalent to $c_DN\le D$ since $D$ is an integer or $\infty$; $D=\infty$ cannot occur once $K>0$). The informal restatement Theorem 1.3 adds the word "explicit"; Theorem 5.9 does not, and no computability requirement is stated.
--
--   Differences from the source:
--   - generalization: constant check (row) weights → row weights and column weights both at most q; reason: the source's proof (Claim 5.1 and the binary-expansion paragraph of the proof of Theorem 5.9) bounds both; dropping the column clauses gives exactly the source's conclusion
--   - encoding: an infinite family of codes with K = Ω(N), D = Ω(N) → for every n₀ a code with N ≥ n₀, constants quantified before n₀, ceiling of c_D N compared in ℕ∞; reason: same family statement; the distance is an integer or +∞ (empty minimum)
--   - encoding: fraction of violated checks at least κ times relative distance → κ·dist·m ≤ N·|Hx|; reason: division-free form, identical for m, N > 0 and trivially true otherwise
-- source:
--   Mitali Bafna, Anqi Li, Quynh T. Nguyen, STOC 2027 submission #1136 (October 2026), Theorem 5.9, printed p.21 (PDF p.22); Definitions 1.1–1.2, printed p.1 (PDF p.2); proof on printed p.22 (PDF p.23)

import Mathlib
import Definitions.Def_GoodQLTC_IsCSS
import Definitions.Def_GoodQLTC_logicalQubits
import Definitions.Def_GoodQLTC_cssDist
import Definitions.Def_RSVProductQLTC_ProductExpansion_conjecture_5_6
import Definitions.Def_RSVProductQLTC_ProductExpansion_locallyTestable
set_option autoImplicit false

namespace RSVProductQLTC.ProductExpansion

/-- Bafna–Li–Nguyen, Theorem 5.9 (Main Theorem), printed p.21 (PDF p.22): assuming
Conjecture 5.6, there is an infinite family of binary quantum CSS codes on `N` qubits with
`K = Ω(N)` logical qubits, distance `D = Ω(N)`, constant soundness (both the X- and the Z-type
check systems are `κ`-locally testable, Definitions 1.1–1.2) and constant check weights.
The constants are chosen before the family; the family contains codes of every large length
bound `n₀ ≤ N`. Column weights are also bounded (Claim 5.1 and the proof). -/
theorem theorem_5_9 (hc : conjecture_5_6) :
    ∃ (cK cD κ : ℝ) (q : ℕ), 0 < cK ∧ 0 < cD ∧
      ∀ n₀ : ℕ, ∃ (N mX mZ : ℕ) (HX : Matrix (Fin mX) (Fin N) (ZMod 2))
          (HZ : Matrix (Fin mZ) (Fin N) (ZMod 2)),
        n₀ ≤ N ∧ GoodQLTC.IsCSS HX HZ ∧
        cK * (N : ℝ) ≤ (GoodQLTC.logicalQubits HX HZ : ℝ) ∧
        ((⌈cD * (N : ℝ)⌉₊ : ℕ) : ℕ∞) ≤ GoodQLTC.cssDist HX HZ ∧
        IsLocallyTestable κ q HX ∧ IsLocallyTestable κ q HZ ∧
        (∀ j : Fin N, hammingNorm (HX.transpose j) ≤ q) ∧
        (∀ j : Fin N, hammingNorm (HZ.transpose j) ≤ q) := by sorry

end RSVProductQLTC.ProductExpansion
