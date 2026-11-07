-- Prove2me | Theorems.Thm_StochAutoreg_lemma_6_1
-- name    : StochAutoreg.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:19:55.875988+00:00
-- url     : https://prove2.me/theorems/2cb85547-8dda-45f6-abe3-0dd1de6ca85d
-- title:
--   Lemma 6.1 — isolated roots: prescribed laws leave final means elsewhere unchanged
-- statement:
--   For integers $M\ge2$ and $K\ge1$ there are distinct strings $r_1,\dots,r_K$ such that arbitrary one-step laws may be prescribed at $r_jz$ for $z\in\Sigma^\star$, $|z|<M$, while the final law at every prompt other than the $r_j$ is independent of these prescriptions.
--
--   In detail: placements of $K$ strings exist; and for any placement $(b_j)_j$ the roots $r_j=b_j1$ are distinct, the completion $g_\pi$ of Lemma 6.1's proof has $p_{g_\pi}(r_jz)=\pi_j(z)$ for $|z|<M$, and $q^{\mathrm{e2e}-M}_{g_\pi}(x)=q^{\mathrm{e2e}-M}_{g_{\pi'}}(x)$ for all prescriptions $\pi,\pi'$ and every $x$ outside the roots. This is the construction on which both families of Section 7 are built.
--
--   Differences from the source:
--   - generalization: there are distinct strings r₁, …, r_K with the property → placements exist, and every placement b, of any index type, has the property with the explicit completion isolate of the paper's proof; reason: it specializes to the source by taking one placement of Fin K; the proof uses only distinctness and equal length, and M7–M11 use it in this form
--   - encoding: the final law at a prompt is independent of the prescriptions → equality of qE2E at the prompt for any two prescriptions; reason: the final law on {0,1} is determined by its mean
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Lemma 6.1, p.12

import Mathlib
import Definitions.Def_StochAutoreg_IsPlacement
import Definitions.Def_StochAutoreg_root
import Definitions.Def_StochAutoreg_isolate
import Definitions.Def_StochAutoreg_qE2E

namespace StochAutoreg

/-- **Lemma 6.1** (isolated roots). For `M ≥ 2` and `K ≥ 1` there are distinct strings `r₁, …, r_K` such that arbitrary
one-step laws may be prescribed at `r_j z` for `|z| < M`, while the final law at every prompt other than the `r_j` is
independent of these prescriptions. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Lemma 6.1, p.12.

**Formalization Note.** The statement has two parts: placements of size `K` exist, and every placement `b`, of any index
type, has the property with the explicit completion `isolate` of the paper's proof. -/
theorem lemma_6_1 (M K : ℕ) (hM : 2 ≤ M) (hK : 1 ≤ K) :
    (∃ b : Fin K → List Bool, IsPlacement b) ∧
    ∀ {ι : Type} (b : ι → List Bool), IsPlacement b →
      Function.Injective (root b) ∧
      (∀ (π : ι → List Bool → unitInterval) (j : ι) (z : List Bool), z.length < M →
        isolate M b π (root b j ++ z) = π j z) ∧
      ∀ (π π' : ι → List Bool → unitInterval) (x : List Bool), x ∉ Set.range (root b) →
        qE2E (isolate M b π) M x = qE2E (isolate M b π') M x := by sorry

end StochAutoreg
