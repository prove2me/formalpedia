-- Prove2me | Theorems.Thm_QLocalCert_claim_C
-- name    : QLocalCert.claim_C
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:21.444343+00:00
-- url     : https://prove2.me/theorems/b72ccd28-532c-49f8-90c6-1f3e7fd637e1
-- title:
--   Claim C — distinct balanced strings give distinct certificates on the central path
-- statement:
--   Let $\mu\ge1$, $N\ge8$ even, $n=n_\mu(N)$ and $U\ge n$. A side-compatible labelling of the trees $T^{\mathrm{tr}}_{N,\mu}(z,z')$ exists, and for every side-compatible labelling the following holds. Let $\Pi$ be a $\mu$-round dMA protocol on $n$-node networks that decides $\mathrm{TreeEQ}_\mu$ with certificates of at most $b$ bits, completeness $c$ and soundness error $s$, where $0\le s<c\le1$ and $2c-1>s$. For each balanced $z$ let $\Gamma_z$ be a certificate assignment of at most $b$ bits per node under which all nodes of $T^{\mathrm{tr}}_{N,\mu}(z,z)$ (with its labelling) accept with probability at least $c$. Then for distinct balanced $z,t$,
--   $$
--   \big(\Gamma_z(w_1),\dots,\Gamma_z(w_{2\mu})\big)\ne\big(\Gamma_t(w_1),\dots,\Gamma_t(w_{2\mu})\big),
--   $$
--   where $w_1,\dots,w_{2\mu}$ are the internal nodes of the central path, common to all the trees.
--
--   Counting the possible tuples then gives the lower bound of Theorem 29.
--
--   Differences from the source:
--   - generalization: the paper's specific assignment of identifiers and ports (p.42) → existence of a side-compatible labelling, and the claim for every side-compatible labelling; reason: the proof uses only side compatibility; the paper's assignment is one such labelling
--   - generalization: identifier bound with O(n) identifiers → every U ≥ n_µ(N); reason: specializes to the paper's bound
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), proof of Theorem 29, pp.42–43

import Mathlib
import Definitions.Def_QLocalCert_DMA
import Definitions.Def_QLocalCert_TreeEQ
import Definitions.Def_QLocalCert_order
import Definitions.Def_QLocalCert_Labelling

set_option autoImplicit false

namespace QLocalCert

/-- **Claim C** (p.43), in the proof of Theorem 29. "Let z, t ∈ {0, 1}^N be two different balanced
strings. Then (Γ_z(w₁), . . . , Γ_z(w_{2µ})) ≠ (Γ_t(w₁), . . . , Γ_t(w_{2µ})), where w₁, . . . , w_{2µ}
are the nodes of the central path of both T^tr_{N,µ}(z, z) and T^tr_{N,µ}(t, t)."

Context (pp.42–43): µ ≥ 1, even N ≥ 8, a µ-round dMA protocol Π for TreeEQµ with completeness c
and soundness error s, 2c − 1 > s, worst-case certificate size b; the identifiers and ports of the
instances T^tr_{N,µ}(z, z′) are assigned as on p.42; "For each balanced string z ∈ {0, 1}^N, denote
by Γ_z a certificate assignment under which all nodes of T^tr_{N,µ}(z, z) accept with probability
at least c in Π."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), proof of Theorem 29, pp.42–43.

**Formalization Note.**
* All instances `T^tr_{N,µ}(z, z′)` live on `Fin n`, `n = order µ N` (Fact 1), with identifier
  bound `U ≥ n`. The paper's assignment of identifiers and ports is captured by
  `Labelling.SideCompatible` (sides fixed as vertex sets, each side's identifiers and ports
  depending only on its own string, the central path fixed).
* The statement has two parts: such a labelling exists; and for **every** such labelling the
  claim holds (generalization: the paper states it for its own labelling). Without the
  compatibility condition the claim would be false.
* `Γ z` is any admissible (at most `b` bits per node) certificate assignment accepted with
  probability at least `c` on `lab z z`, for each balanced `z`. The tuple
  `(Γ_z(w₁), …, Γ_z(w_{2µ}))` is `fun j => Γ z (L.w j)`. -/
theorem claim_C (μ N U : ℕ) (hμ : 1 ≤ μ) (hN : Even N) (h8 : 8 ≤ N) (hU : order μ N ≤ U) :
    (∃ L : Labelling N μ (order μ N) U, L.SideCompatible) ∧
    ∀ L : Labelling N μ (order μ N) U, L.SideCompatible →
      ∀ (P : DMA (order μ N) U μ) (b : ℕ) (c s : ℝ), 0 ≤ s → s < c → c ≤ 1 → s < 2 * c - 1 →
        P.Correct (TreeEQ μ) b c s →
        ∀ Γ : (Fin N → Bool) → Fin (order μ N) → List Bool,
          (∀ z, Balanced z → (∀ v, (Γ z v).length ≤ b) ∧ c ≤ P.acceptProb (L.lab z z) (Γ z)) →
          ∀ z t : Fin N → Bool, Balanced z → Balanced t → z ≠ t →
            (fun j => Γ z (L.w j)) ≠ (fun j => Γ t (L.w j)) := by sorry

end QLocalCert
