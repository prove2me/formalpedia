-- Prove2me | Theorems.Thm_SigGolfCandidate_Memory_digit_fold
-- name    : SigGolfCandidate.Memory.digit_fold
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-27T19:39:42.46983+00:00
-- url     : https://prove2.me/theorems/ea9630c6-c709-4e60-9071-7f1b64e9b6fe
-- title:
--   Reconstruct a number prefix from fixed-width digits
-- statement:
--   Reconstruct a number prefix from fixed-width digits.
--
--   Public Apache-2.0 source, inherited from the baseline imported by gpsanant in commit 371a7d65bc8740c69b9f5da32d135b34ede3a80b; original lemma authorship is not established. Verified Yukon submission b288fe22-f009-4560-ac67-b630b212909d by saucegodbased reuses it. Source and target Lean/Mathlib pins match. This is a selected arithmetic helper, not the full signature verifier.
-- source:
--   https://github.com/Layr-Labs/sig.golf-submission-dev/blob/bb47bcecd5287432ffff11ae37ce75ff9eb91646/submission/SigGolfCandidate/Memory.lean#L97-L106
--
--   yukon-proof-operation:bootstrap-f548a4db07c5745c40a2800b5b67e5d23361717c9acd2f87af867186f2f445d6
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Ym9vdHN0cmFwLWY1NDhhNGRiMDdjNTc0NWM0MGEyODAwYjViNjdlNWQyMzM2MTcxN2M5YWNkMmY4N2FmODY3MTg2ZjJmNDQ1ZDYiLCJoYXNoIjoiNDE4ZWZlZmU4ZjM3M2FhMjEyMTFlM2EwMGM5MjAwZDc0MGU1NzI2OTk4YjgxZjUzYTZmN2NlMGRmNDAwZDBjZCIsImtpbmQiOiJwcm9ibGVtIiwidGFyZ2V0IjoiU2lnR29sZkNhbmRpZGF0ZS5NZW1vcnkuZGlnaXRfZm9sZCIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6InNpZy1nb2xmIn0]

import Mathlib
namespace SigGolfCandidate.Memory

theorem digit_fold (x width n initial : Nat) :
    (List.range n).foldl (fun acc i => acc + (x / 2 ^ (width * i) % 2 ^ width) * 2 ^ (width * i)) initial =
      initial + x % 2 ^ (width * n) := by sorry
end SigGolfCandidate.Memory
