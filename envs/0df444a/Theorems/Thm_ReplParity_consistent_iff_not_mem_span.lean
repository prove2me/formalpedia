-- Prove2me | Theorems.Thm_ReplParity_consistent_iff_not_mem_span
-- name    : ReplParity.consistent_iff_not_mem_span
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:31.780034+00:00
-- url     : https://prove2.me/theorems/5c3c4f47-f7b2-4c81-983e-3c04f3db91e2
-- title:
--   §2.1, p.11 — a sample is consistent with a parity iff $e_{d+1}\notin\mathrm{span}(S)$ [NST26, Claim 3]
-- statement:
--   Let $S=((x_1,y_1),\dots,(x_m,y_m))$ be a sample of labeled examples over $\mathbb F_2^d$, and identify each example with its lifted vector $(x_i,y_i)\in\mathbb F_2^{d+1}$.
--
--   1. For every $z\in\mathbb F_2^d$, the parity $f_z$ is consistent with $S$ (that is, $\langle z,x_i\rangle=y_i$ for all $i$) if and only if every lifted vector lies in the hyperplane $G_z=\{(x,\langle z,x\rangle)\}$.
--   2. $S$ is consistent with some parity if and only if
--   $$e_{d+1}\notin\mathrm{span}\{(x_i,y_i):i\le m\}.$$
--
--   This is the bridge between parity learning and span computations used by the learner of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: a sample S and the hyperplane G_z = {(x, ⟨z, x⟩)} → a finite sequence S : Fin m → 𝔽ᵈ₂ × 𝔽₂, and G_z = {v : ⟨z, v'⟩ = v_{d+1}}; reason: same sample and same set; labels {0,1} read in 𝔽₂
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.1, p.11 (PDF p.13), citing [NST26, Claim 3]

import Mathlib
import Definitions.Def_ReplParity_parity

namespace ReplParity

/-- **Consistency of a sample with a parity [NST26, Claim 3].** Shen, Zhong, *Replicable Parity
Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript
sha256 40424491…), §2.1, p.11 (PDF p.13): "A parity f_z is consistent with a sample S exactly when
every lifted vector lies in the hyperplane G_z = {(x, ⟨z, x⟩) : x ∈ 𝔽ᵈ₂}, and so S is consistent
with some parity exactly when e_{d+1} ∉ span(S) [NST26, Claim 3]."

(a) `f_z` agrees with every example of `S` iff every lifted example lies in `G_z`;
(b) some parity agrees with every example of `S` iff `e_{d+1}` is outside the span of the lifted
examples. -/
theorem consistent_iff_not_mem_span (d m : ℕ) (S : Fin m → Example d) :
    (∀ z : Vec d, (∀ i, parity z (S i).1 = (S i).2) ↔ ∀ i, lift (S i) ∈ hyperplaneG z) ∧
    ((∃ z : Vec d, ∀ i, parity z (S i).1 = (S i).2) ↔
      eLast d ∉ Submodule.span (ZMod 2) (Set.range (fun i => lift (S i)))) := by sorry

end ReplParity
