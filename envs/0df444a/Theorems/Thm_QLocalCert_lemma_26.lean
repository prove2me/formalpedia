-- Prove2me | Theorems.Thm_QLocalCert_lemma_26
-- name    : QLocalCert.lemma_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:58.069213+00:00
-- url     : https://prove2.me/theorems/45fb8d9d-c8e1-4298-978d-a184186c5ef0
-- title:
--   Lemma 26 — $T^{\mathrm{tr}}_{N,\mu}(z,z')\cong T^{\mathrm{tr}}_{\hat N,\mu}(\hat z,\hat z')$ iff $N=\hat N$ and $(z,z')\in\{(\hat z,\hat z'),(\hat z',\hat z)\}$
-- statement:
--   For every $\mu\ge1$, even $N,\hat N\ge8$, balanced $z,z'\in\{0,1\}^N$ and balanced $\hat z,\hat z'\in\{0,1\}^{\hat N}$,
--   $$
--   T^{\mathrm{tr}}_{N,\mu}(z,z')\cong T^{\mathrm{tr}}_{\hat N,\mu}(\hat z,\hat z')\iff N=\hat N\ \text{and}\ \big((z,z')=(\hat z,\hat z')\ \text{or}\ (z,z')=(\hat z',\hat z)\big).
--   $$
--
--   The unordered pair of encoded strings is thus an isomorphism invariant. In particular $T^{\mathrm{tr}}_{N,\mu}(z,t)\notin\mathrm{TreeEQ}_\mu$ for $z\ne t$, the no-instance used in Claim C.
--
--   Differences from the source:
--   - encoding: N = N̂ and (z, z′) = (ẑ, ẑ′) or (ẑ′, ẑ) → ∃ h : N = N', z = w ∘ Fin.cast h ∧ … (strings of different types compared along h); reason: z and ẑ live in different types Fin N → Bool and Fin N̂ → Bool
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Lemma 26, p.37

import Mathlib
import Definitions.Def_QLocalCert_Ttr

set_option autoImplicit false

namespace QLocalCert

/-- **Lemma 26** (p.37). "For every µ ≥ 1, even N, N̂ ≥ 8, strings z, z′ ∈ {0, 1}^N of Hamming
weight N/2, and strings ẑ, ẑ′ ∈ {0, 1}^N̂ of Hamming weight N̂/2, it holds that
T^tr_{N,µ}(z, z′) ≅ T^tr_{N̂,µ}(ẑ, ẑ′) if and only if N = N̂ and (z, z′) = (ẑ, ẑ′) or
(z, z′) = (ẑ′, ẑ)."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Lemma 26, p.37.

**Formalization Note.** `N̂` is `N'`, `ẑ, ẑ′` are `w, w'`. Since `z` and `w` have the types
`Fin N → Bool` and `Fin N' → Bool`, the equality of strings is stated through `h : N = N'` as
`z = w ∘ Fin.cast h`. -/
theorem lemma_26 (μ N N' : ℕ) (hμ : 1 ≤ μ) (hN : Even N) (hN' : Even N') (h8 : 8 ≤ N)
    (h8' : 8 ≤ N') (z z' : Fin N → Bool) (w w' : Fin N' → Bool) (hz : Balanced z)
    (hz' : Balanced z') (hw : Balanced w) (hw' : Balanced w') :
    Nonempty (Ttr N μ z z' ≃g Ttr N' μ w w') ↔
      ∃ h : N = N', (z = w ∘ Fin.cast h ∧ z' = w' ∘ Fin.cast h) ∨
        (z = w' ∘ Fin.cast h ∧ z' = w ∘ Fin.cast h) := by sorry

end QLocalCert
