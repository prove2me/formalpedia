-- Prove2me | Theorems.Thm_ShamirLLR_lemma_2_1
-- name    : ShamirLLR.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:58.940455+00:00
-- url     : https://prove2.me/theorems/1e324b80-4843-43be-a167-8d68b21d32d1
-- title:
--   Lemma 2.1 — simultaneous Cauchy–Schwarz
-- statement:
--   Let $p$ be an odd prime and $\eta>0$. Let $\mathcal H$ be a class of probability maps closed under bijective affine precomposition ($g\in\mathcal H$, $\theta(z)=\lambda z+\mu$, $\lambda\in\mathbb F_p^*$ imply $g\circ\theta\in\mathcal H$), such that every $f:\mathbb F_p\to\{0,1\}$ has some $g\in\mathcal H$ with $\|f-g\|_{U^3(\mathbb F_p)}\le\eta$. Let $1\le r<m$ and let $a$ be an ordered tuple of distinct nonzero evaluation places. If $t$ is an integer with $1\le t<r$ and $m-t\le3(r-t)$, then
--   $$
--   \Delta(a;r)\le\sum_{J\subseteq[m],\ |J|<t}2^{|J|}\,\Delta_{\mathcal H}(a_{J^c};r-|J|)+4^m\eta^t .
--   $$
--
--   This reduces arbitrary one-bit leakage to structured leakage; the condition $m-t\le3(r-t)$ is where $c>1/3$ enters.
--
--   Differences from the source:
--   - encoding: $a_{J^c}=(a_i)_{i\in J^c}$, a tuple of length $m-|J|$ → the restriction of $a$ to the subtype $\{i\mid i\notin J\}$; reason: $\Delta$ is defined for any finite index type and is invariant under reindexing
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Lemma 2.1, Eq. (9), p.14 (PDF p.15); standing assumption $1\le r<m$, §2, p.13

import Mathlib
import Definitions.Def_ShamirLLR_evalTuples
import Definitions.Def_ShamirLLR_leakageLaws
import Definitions.Def_ShamirLLR_deltaClass
import Definitions.Def_ShamirLLR_gowersU3

set_option autoImplicit false

namespace ShamirLLR

/-- **Lemma 2.1 (Simultaneous Cauchy–Schwarz).** Fix `η > 0`. Let `𝓗` be a class of probability
maps closed under bijective affine precomposition, such that every `f : 𝔽_p → {0,1}` has some
`g ∈ 𝓗` with `‖f − g‖_{U³(𝔽_p)} ≤ η`. Let `1 ≤ r < m`. For every ordered tuple `a` of distinct
nonzero places and every integer `t` with `1 ≤ t < r` and `m − t ≤ 3(r − t)`,
`Δ(a; r) ≤ ∑_{J ⊆ [m], |J| < t} 2^{|J|} Δ_𝓗(a_{J^c}; r − |J|) + 4^m η^t`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Lemma 2.1, Eq. (9), p.14; standing assumption `1 ≤ r < m`, §2, p.13.

**Formalization Note.** `a_{J^c}` is the restriction of `a` to `{i // i ∉ J}`. -/
theorem lemma_2_1 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (η : ℝ) (hη : 0 < η)
    (H : Set (ZMod p → ℝ)) (hHprob : ∀ g ∈ H, IsProbMap g)
    (hHaff : ∀ g ∈ H, ∀ l μ : ZMod p, l ≠ 0 → (fun z => g (l * z + μ)) ∈ H)
    (hHapprox : ∀ f : ZMod p → Bool, ∃ g ∈ H,
      gowersU3 (fun z => ((bitMap f z - g z : ℝ) : ℂ)) ≤ η)
    (m r : ℕ) (hr : 1 ≤ r) (hrm : r < m) (a : Fin m → ZMod p) (ha : a ∈ evalTuples p m)
    (t : ℕ) (ht : 1 ≤ t) (htr : t < r) (hmt : m - t ≤ 3 * (r - t)) :
    delta a r ≤
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.card < t),
          (2 : ℝ) ^ J.card * deltaClass H (fun i : {i : Fin m // i ∉ J} => a i) (r - J.card) +
        (4 : ℝ) ^ m * η ^ t := by sorry

end ShamirLLR
