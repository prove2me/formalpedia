-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_D_9
-- name    : QuantumKtSoI.Supplement.theorem_D_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:50:32.94179+00:00
-- url     : https://prove2.me/theorems/bad2f9ce-103e-4941-8469-dcabe3dc134e
-- title:
--   Theorem D.9, p.153 — the scheduled evaluation halts with output $w$ within $K_D(\mathrm{ad}(f))\,t$ units with probability at least $P_f(z;t,w)$
-- statement:
--   Let $D\ge1$ be an integer. For every description $f$, every string $z$, every string $w$ and every integer $t\ge0$,
--   $$\Pr\big[\mathrm{sim}^D_f(z)\text{ halts with output }w\text{ and }\lambda\le K_D(\mathrm{ad}(f))\,t\big]\ge P_f(z;t,w),$$
--   where $\mathrm{sim}^D_f(z)=(\lambda,o)$ is the scheduled evaluation of Definition D.7, $\mathrm{ad}(f)$ is the amplification depth and $K_D(a)=\sum_{j=0}^a(1+1/D)^j$. If $D\ge\mathrm{ad}(f)$, then $K_D(\mathrm{ad}(f))\le3(\mathrm{ad}(f)+1)$.
--
--   This dilation bound is the accounting behind the quasi-linear interpreter of Appendix D.
--
--   **Formalization Note** "Halts with output $w$" is $o=w$, so $\lambda<\infty$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: the random pair sim^D_f(z) and the probability of an event → its law as a mass function on outcomes; the probability of the event is the sum of the masses of (s, w) over integers s ≤ K_D(ad(f))·t, compared in [0,∞]; reason: a discrete law is its mass function
--   - encoding: f^{hz}_f(h, w): the weight of the complete record sequences of length h with output w → P_f(z; h, w) − P_f(z; h−1, w) (and P_f(z; 0, w) at h = 0); reason: the identity P_f(z; s, w) = Σ_{h ≤ s} f^{hz}_f(h, w) stated on p.149
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem D.9, p.153; Definition D.7, p.152

import Mathlib
import Definitions.Def_QuantumKtSoI_Supplement_simLaw

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem D.9** (Dilation of the scheduled evaluation; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.153). Let `D ≥ 1` be an integer.
For every description `f`, every string `z`, every string `w` and every integer `t ≥ 0`,
`Pr[sim^D_f(z) halts with output w and λ ≤ K_D(ad(f)) t] ≥ P_f(z; t, w)`. If `D ≥ ad(f)`, then
`K_D(ad(f)) ≤ 3(ad(f) + 1)`.

**Formalization Note** `sim^D_f(z)` is the random pair of Definition D.7, given by its mass
function `simLaw G D f z` on outcomes `(λ, o) ∈ ℕ∞ × Option {0,1}*`; "halts with output `w`" is
`o = w` (so `λ < ∞`), and the probability of the event is the sum of the masses of `(s, w)` over the
integers `s ≤ K_D(ad(f)) t`, compared in `ℝ≥0∞`. `P_f` and the scheduled evaluation use the
admissible glue routine set `G` (p.24). -/
theorem theorem_D_9 (G : GlueRoutines) (hG : G.Admissible) (D : ℕ) (hD : 1 ≤ D) :
    (∀ (f : Desc) (z w : List Bool) (t : ℕ),
      ENNReal.ofReal (f.prob G z t w) ≤
        ∑' s : ℕ, if (s : ℝ) ≤ KD D (ad f) * t then simLaw G D f z ((s : ℕ∞), some w) else 0) ∧
    ∀ f : Desc, ad f ≤ D → KD D (ad f) ≤ 3 * ((ad f : ℝ) + 1) := by sorry

end QuantumKtSoI.Supplement
