-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_claim_4_9
-- name    : RecoveryStorage3SUM.Adaptive.claim_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:40.259218+00:00
-- url     : https://prove2.me/theorems/11f9161f-e2cd-425c-8a49-a40ffa86a4f4
-- title:
--   Claim 4.9 — $z(c)$ never undercounts, and is exact in a clean complete run
-- statement:
--   Fix $A'\subseteq A$, $B'\subseteq B$, a run with prime $p$, arbitrary inverter answers, a target $c$, and $r=c\bmod p$. Then
--   $$z(c)\ge\mathrm{count}_{A'\times B'}(c).$$
--   If moreover the run is clean for $c$ and Recover$(r)$ outputs all of $M_r$, then $z(c)=\mathrm{count}_{A'\times B'}(c)$.
--
--   This is why answering yes iff the minimum of $z_j(c)$ is positive is correct when some run is clean and complete, and why a target with a pair is never answered no.
--
--   Differences from the source:
--   - generalization: the source run, the cap L and its FN answers with bounded equal-size inputs and a sampled R → arbitrary finite integer sets A, B and R and integer target c, arbitrary inverter answers and partitions, any cap, any K and L, and any positive modulus p; the queried subsets remain subsets of A and B; reason: the inequality and conditional equality use the verified-output inclusion and cleanliness only, so all source instances specialize directly
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Claim 4.9, p.13

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Construction

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

/-- Claim 4.9, p.13: for every target `c` and run, `z(c) ≥ count_{A′×B′}(c)`; if moreover the run is
clean for `c` and `Recover(r)` outputs all of `M_r`, where `r = c mod p`, then `z(c) = count_{A′×B′}(c)`. -/
theorem claim_4_9 {A : Finset ℤ} {K L : ℕ} (B R A' B' : Finset ℤ) (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (run : Attempt A K L) (inv : Fin K → Fin L → ℕ → Option ℕ) (cap : ℕ) (hp : 0 < run.p) (c : ℤ) :
    let r := residue run.p c
    let out := recoverOutput B R run inv cap r
    (countIn A' B' c : ℤ) ≤ zValue A' B' run.p out c ∧
      (CleanFor B R run.p c → out = unmarkedClass A B R run.p r →
        zValue A' B' run.p out c = (countIn A' B' c : ℤ)) := by sorry

end RecoveryStorage3SUM.Adaptive
