-- Prove2me | Theorems.Thm_StretchDepth_divergence_implies_mem_Q
-- name    : StretchDepth.divergence_implies_mem_Q
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:07.133198+00:00
-- url     : https://prove2.me/theorems/8f5b577f-f99a-4211-90f6-7b5a568a5ba0
-- title:
--   Proof of Theorem 1 — a divergence from the reference forces $w\in Q$
-- statement:
--   Let $t$ be a deterministic query procedure (the reduction on the challenge $z$ under a fixed draw), and fix $G,S,w,z$. Put $G'=G[w\mapsto z]$, $T=T_{G|_{\overline S}}$, $T'=T_{G'|_{\overline S}}$, $S^+=S\cup\{w\}$ and $T^+=T_{G|_{\overline{S^+}}}$. If $w\notin Q$, then
--   $$
--   t^{G',T'}=t^{G,T^+}=t^{G,T},
--   $$
--   that is, the planted and the unplanted executions both agree with the reference execution: on every query of the reference execution $t^{G,T^+}$, the oracle pair $(G',T')$ and the pair $(G,T)$ each return the reference answer, so all three executions follow the same path with the same answers and the same output.
--
--   So a difference between the two real experiments can occur only when the uniform point $w$ lands in the small set $Q$.
--
--   Differences from the source:
--   - encoding: rho = G|_{S̄} with S the free set (overline on the rendered p.13, p.20) → freeOn G S; reason: notation only, the same partial assignment
--   - reading: x, F chosen canonically depending only on rho+, y → any choice function wit on (rho, y) valid where T_rho(y) = 1; reason: the canonical choice is one such function, so the page gives no more specific object
--   - generalization: N > n, M > m and the setting of Theorem 1 → no condition on the parameters; reason: the argument uses none of them, and every instance of the source is covered
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Theorem 1, pp.20–21

import Definitions.Def_StretchDepth_Qset

namespace StretchDepth

/-- **Proof of Theorem 1: a divergence forces `w ∈ Q`.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Theorem 1, p.20: "We need to show that whenever one of the planted/unplanted
executions differs from the reference we must have w ∈ Q."

Here `G′ = G[w ↦ z]`, `T = T_{G|_{S̄}}`, `T′ = T_{G′|_{S̄}}`, `S⁺ = S ∪ {w}`, `T⁺ = T_{G|_{S⁺̄}}`; the
planted execution is `R^{G′,T′}(z)`, the unplanted `R^{G,T}(z)` and the reference `R^{G,T⁺}(z)`,
with `R(z)` the deterministic procedure `t`.

**Formalization Note.** The statement holds for every procedure `t` and every `z`; `Q` is built
from any witness choice valid at each `(ρ, y)` (`IsWitness`). "The executions agree" is stated in
full: on every query of the reference execution the planted (resp. unplanted) oracle gives the
reference answer, so all three executions follow the same path with the same answers; the
equality of outputs is stated as well. -/
theorem divergence_implies_mem_Q {n N m M : ℕ} (H : Bits m → RoundTree n N M)
    (wit : PartialAssign n N → Bits M → Bits m × (Bits n → Bits N)) (hwit : IsWitness H wit)
    (t : QProc n N M) (G : Bits n → Bits N) (S : Finset (Bits n)) (w : Bits n) (z : Bits N)
    (hw : w ∉ Qset H wit t G (insert w S)) :
    (∀ i ∈ pathQueries t (oracle G (testOf H (freeOn G (insert w S)))),
        oracle (Function.update G w z) (testOf H (freeOn (Function.update G w z) S)) i =
          oracle G (testOf H (freeOn G (insert w S))) i) ∧
      (∀ i ∈ pathQueries t (oracle G (testOf H (freeOn G (insert w S)))),
        oracle G (testOf H (freeOn G S)) i = oracle G (testOf H (freeOn G (insert w S))) i) ∧
      t.eval (oracle (Function.update G w z) (testOf H (freeOn (Function.update G w z) S))) =
        t.eval (oracle G (testOf H (freeOn G (insert w S)))) ∧
      t.eval (oracle G (testOf H (freeOn G S))) =
        t.eval (oracle G (testOf H (freeOn G (insert w S)))) := by sorry

end StretchDepth
